`default_nettype none
`define assert(condition) if(!((|{condition})===1)) begin $display("FAIL"); $finish(1); end

module ram #(
  parameter integer LGSZW = 8
) (
  input wire clk,
  input wire [LGSZW-1:0] addr,
  input wire write_enable,
  input wire [31:0] write,
  output reg [31:0] read
);
  parameter integer SZW = (1<<LGSZW);
  reg [7:0] byte0 [0:SZW-1];
  reg [7:0] byte1 [0:SZW-1];
  reg [7:0] byte2 [0:SZW-1];
  reg [7:0] byte3 [0:SZW-1];
  always @(posedge clk) begin
    read[ 7: 0] <= byte0[addr];
    read[15: 8] <= byte1[addr];
    read[23:16] <= byte2[addr];
    read[31:24] <= byte3[addr];
    if (write_enable) byte0[addr] <= write[ 7: 0];
    if (write_enable) byte1[addr] <= write[15: 8];
    if (write_enable) byte2[addr] <= write[23:16];
    if (write_enable) byte3[addr] <= write[31:24];
  end
endmodule

module system(input wire clk, input wire reset, output wire led);
    // reg clk=0, reset=1;
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
      .addr(mem_rq_addr[LGSZW-1+2:2]),
      .write_enable(mem_rq_iswrite && ((mem_rq_addr >> (2+LGSZW)) == 0)),
      .read(ram_read),
      .write(0)
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

    // always #1 clk = !clk;
    // initial begin 
    //   $readmemh("program.hex", ram.byte0);
    //   $readmemh("program.hex", ram.byte1);
    //   $readmemh("program.hex", ram.byte2);
    //   $readmemh("program.hex", ram.byte3);
    //   $dumpfile("system.vcd");
    //   $dumpvars(1, clk, reset, mem_rq_addr, mem_rq_iswrite, mem_rq_data, rdy_obtain_rq_get, en_obtain_rq_get, rdy_send_rs_put, en_send_rs_put, send_rs_put);
    //   #2 reset <= 0;
    //   #1000 $finish();
    // end 
    assign led = ram_read[0];
endmodule
