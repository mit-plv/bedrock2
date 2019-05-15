`default_nettype none
`define assert(condition) if(!((|{condition})===1)) begin $display("FAIL"); #1 $finish(1); end

// byte-addressable word memory built from 4 byte-addressable byte memories
module ram #(
  parameter integer LGSZW = 8
) (
  input wire clk,
  input wire [LGSZW+1:0] addr,
  input wire write_enable,
  input wire [31:0] write,
  output reg [31:0] read
);
  parameter integer SZW = (1<<LGSZW);

  reg [7:0] byte0[0:SZW-1];
  reg [7:0] byte1[0:SZW-1];
  reg [7:0] byte2[0:SZW-1];
  reg [7:0] byte3[0:SZW-1];
  initial begin 
    $readmemh("program0.hex", byte0);
    $readmemh("program1.hex", byte1);
    $readmemh("program2.hex", byte2);
    $readmemh("program3.hex", byte3);
  end

  wire [1:0] align = addr[1:0];
  reg [1:0] delay_align = 2'h0;
  wire [LGSZW-1:0] addr_ [4];
  reg [7:0] write_ [4]; // wire
  reg [7:0] read_ [4];

  generate genvar i; for (i=0; i<4; i=i+1) begin
    assign addr_[i] = addr[LGSZW+1:2]+(align>i);
    always @(*) begin
      case (align)
        2'h0: write_[i] = write[8*(i-2'h0)+7:8*(i-2'h0)];
        2'h1: write_[i] = write[8*(i-2'h1)+7:8*(i-2'h1)];
        2'h2: write_[i] = write[8*(i-2'h2)+7:8*(i-2'h2)];
        2'h3: write_[i] = write[8*(i-2'h3)+7:8*(i-2'h3)];
      endcase
    end
  end endgenerate

  always @(*) begin
    case (delay_align)
      2'h0: read = {read_[3], read_[2], read_[1], read_[0]};
      2'h1: read = {read_[0], read_[3], read_[2], read_[1]};
      2'h2: read = {read_[1], read_[0], read_[3], read_[2]};
      2'h3: read = {read_[2], read_[1], read_[0], read_[3]};
    endcase
  end

  always @(posedge clk) begin
    read_[0] <= byte0[addr_[0]];
    read_[1] <= byte1[addr_[1]];
    read_[2] <= byte2[addr_[2]];
    read_[3] <= byte3[addr_[3]];
    if (write_enable) byte0[addr_[0]] <= write_[0];
    if (write_enable) byte1[addr_[1]] <= write_[1];
    if (write_enable) byte2[addr_[2]] <= write_[2];
    if (write_enable) byte3[addr_[3]] <= write_[3];

    delay_align <= addr[1:0];
  end
endmodule

module system;
    reg clk=0, reset=1;

// module system(input wire clk, input wire reset, output wire led);

    wire [64:0] obtain_rq_get;
    wire rdy_obtain_rq_get;
    wire en_obtain_rq_get;
    wire [31:0] send_rs_put;
    wire rdy_send_rs_put;
    reg en_send_rs_put = 0;
    mkTop mkTop(.CLK(clk),
                .RST_N(~reset),
                .EN_obtain_rq_get(en_obtain_rq_get),
                .obtain_rq_get(obtain_rq_get),
                .RDY_obtain_rq_get(rdy_obtain_rq_get),

                .send_rs_put(send_rs_put),
                .EN_send_rs_put(en_send_rs_put),
                .RDY_send_rs_put(rdy_send_rs_put)
              );
    wire [31:0] mem_rq_data = obtain_rq_get[31:0];
    wire mem_rq_iswrite = obtain_rq_get[32];
    wire [31:0] mem_rq_addr = obtain_rq_get[64:33];

    parameter integer LGSZW = 8;
    wire [31:0] ram_read;
    ram #(.LGSZW(LGSZW)) ram (
      .clk(clk), 
      .addr(mem_rq_addr[LGSZW-1+2:0]),
      .write_enable(rdy_obtain_rq_get && mem_rq_iswrite && ((mem_rq_addr >> (2+LGSZW)) == 0)),
      .read(ram_read),
      .write(mem_rq_data)
    );

    assign en_obtain_rq_get = (rdy_obtain_rq_get && ((mem_rq_addr >> (2+LGSZW)) == 0));
    assign send_rs_put = (en_send_rs_put && ((mem_rq_addr >> (2+LGSZW)) == 0) ? ram_read : 32'hxxxxxxxx);
    always @(posedge clk) begin
      if (en_obtain_rq_get) begin
        en_send_rs_put <= 1'b1;
      end else if (en_send_rs_put) begin
        //`assert(rdy_send_rs_put)
        en_send_rs_put <= 1'b0;
      end 
    end

    always #1 clk = !clk;
    initial begin 
      $dumpfile("system.vcd");
      $dumpvars(1, clk, reset,
        mem_rq_addr, mem_rq_iswrite, mem_rq_data, rdy_obtain_rq_get, en_obtain_rq_get, rdy_send_rs_put, en_send_rs_put, send_rs_put);
      #2 reset <= 0;
      #1000 $finish();
    end 
    // assign led = mem_rq_addr[0];
endmodule
