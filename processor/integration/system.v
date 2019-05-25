`default_nettype none
`ifdef SYNTHESIS
`define assert(condition)
`else
`define assert(condition) if(!((|{condition})===1)) begin $display("FAIL"); #1 $finish(1); end
`endif

// byte-addressable word memory built from 4 byte-addressable byte memories
module ram #(
  parameter integer LGSZW = 8
) (
  input wire clk,
  input wire [LGSZW+1:0] addr,
  input wire write_enable,
  input wire [31:0] write,
  input wire rq_en, // always ready
  output reg rs_en = 0, // user must be always ready
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

  wire [1:0] rq_align = addr[1:0];
  reg [1:0] rs_align = 2'h0;
  wire [LGSZW-1:0] addr_ [4];
  reg [7:0] write_ [4]; // wire
  reg [7:0] read_ [4];
  wire [3*32-1:0] write_write_write = {write, write, write};

  generate genvar i; for (i=0; i<4; i=i+1) begin
    assign addr_[i] = addr[LGSZW+1:2]+(rq_align>i);
    always @(*) begin
      case (rq_align)
        2'h0: write_[i] = write_write_write[32+8*(i-2'h0)+7:32+8*(i-2'h0)];
        2'h1: write_[i] = write_write_write[32+8*(i-2'h1)+7:32+8*(i-2'h1)];
        2'h2: write_[i] = write_write_write[32+8*(i-2'h2)+7:32+8*(i-2'h2)];
        2'h3: write_[i] = write_write_write[32+8*(i-2'h3)+7:32+8*(i-2'h3)];
      endcase
    end
  end endgenerate

  always @(*) begin
    case (rs_align)
      2'h0: read = {read_[3], read_[2], read_[1], read_[0]};
      2'h1: read = {read_[0], read_[3], read_[2], read_[1]};
      2'h2: read = {read_[1], read_[0], read_[3], read_[2]};
      2'h3: read = {read_[2], read_[1], read_[0], read_[3]};
    endcase
  end

  always @(posedge clk) begin
    rs_en <= rq_en;
    rs_align <= rq_align;
    if (rq_en && !write_enable) begin
      read_[0] <= byte0[addr_[0]];
      read_[1] <= byte1[addr_[1]];
      read_[2] <= byte2[addr_[2]];
      read_[3] <= byte3[addr_[3]];
    end else if (rq_en && write_enable) begin
      byte0[addr_[0]] <= write_[0];
      byte1[addr_[1]] <= write_[1];
      byte2[addr_[2]] <= write_[2];
      byte3[addr_[3]] <= write_[3];
    end
  end
endmodule

module system(
`ifdef SYNTHESIS
  input wire clk,
`endif
  output reg [7:0] led = 8'hff
);
  reg spi_clk = 0;
  reg spi_cs = 0;
  wire spi_mosi;
  wire spi_miso;

`ifndef SYNTHESIS
  reg clk=0;
`endif

  reg resetn = 1'b0; always @(posedge clk) begin resetn <= 1'b1; end

  parameter integer LGSZW = 8;
  wire [31:0] ram_read;
  wire [64:0] obtain_rq_get;
  wire rdy_obtain_rq_get;
  wire en_obtain_rq_get = rdy_obtain_rq_get;
  wire rdy_send_rs_put;
  wire [31:0] mem_rq_data = obtain_rq_get[31:0];
  wire mem_rq_iswrite = obtain_rq_get[32];
  wire [31:0] mem_rq_addr = obtain_rq_get[64:33];
  wire rq_addr_is_bram = ((mem_rq_addr >> (2+LGSZW)) == 0);
  wire ram_rs_en, instant_rs_en;
  wire [31:0] instant_rs;
  mkTop mkTop(.CLK(clk),
              .RST_N(resetn),
              .EN_obtain_rq_get(en_obtain_rq_get),
              .obtain_rq_get(obtain_rq_get),
              .RDY_obtain_rq_get(rdy_obtain_rq_get),

              .send_rs_put(ram_rs_en ? ram_read
                           : instant_rs_en ? instant_rs 
	                   : 32'hxxxxxxxx),
              .EN_send_rs_put(ram_rs_en || instant_rs_en),
              .RDY_send_rs_put(rdy_send_rs_put)
            );
  ram #(.LGSZW(LGSZW)) ram (
    .clk(clk),
    .addr(mem_rq_addr[LGSZW-1+2:0]),
    .write_enable(mem_rq_iswrite),
    .rq_en(en_obtain_rq_get && rdy_obtain_rq_get && rq_addr_is_bram),
    .rs_en(ram_rs_en),
    .read(ram_read),
    .write(mem_rq_data)
  );

  assign instant_rs_en = en_obtain_rq_get && (mem_rq_addr == 32'h1001200c || mem_rq_addr == 32'h10024048 || mem_rq_addr == 32'h1002404c);
  assign instant_rs =
	  (!instant_rs_en) ? 32'hxxxxxxxx
	  : (mem_rq_addr == 32'h1001200c && !mem_rq_iswrite) ? {8'h00, led, 16'h0000}
	  : (mem_rq_addr == 32'h10024048 && !mem_rq_iswrite) ? {(!spi_tx_rdy), 31'h0}
	  : (mem_rq_addr == 32'h1002404c && !mem_rq_iswrite) ? {(!spi_tx_rdy), 23'h0, spi_rx_buf}
	  : 32'hxxxxxxxx;
  always @(posedge clk) begin
    if (en_obtain_rq_get && mem_rq_iswrite && mem_rq_addr == 32'h1001200c) begin
      led <= mem_rq_data[23:16];
    end
  end
  wire spi_tx_en = en_obtain_rq_get && mem_rq_iswrite && mem_rq_addr == 32'h1001200c;
  reg [3:0] spi_tx_remaining = 0;
  reg [7:0] spi_tx_buf;
  reg [7:0] spi_rx_buf;
  assign spi_mosi = spi_tx_buf[7];
  wire spi_tx_rdy = (spi_clk == 0 && spi_tx_remaining == 0);
  always @(posedge clk) begin
    if (spi_tx_rdy && spi_tx_en) begin
      spi_tx_buf <= mem_rq_data[7:0];
      spi_tx_remaining <= 8;
    end else if (spi_tx_remaining && !spi_clk) begin
      spi_clk <= 1;
      spi_rx_buf = {spi_rx_buf[6:0], spi_mosi};
    end else if (spi_clk) begin
      spi_clk <= 0;
      spi_tx_buf <= {spi_tx_buf[6:0], 1'bx};
      spi_tx_remaining <= spi_tx_remaining - 1;
    end
  end

`ifndef SYNTHESIS
  always #1 clk = !clk;
  initial begin
    $dumpfile("system.vcd");
    $dumpvars(1, led, spi_clk, spi_cs, spi_mosi, spi_miso, clk, resetn,
      rdy_obtain_rq_get, en_obtain_rq_get, mem_rq_iswrite, mem_rq_addr, mem_rq_data, rdy_send_rs_put, ram_rs_en, instant_rs_en, ram_read, spi_tx_buf, spi_rx_buf, mkTop.proc_m8_pc);
    #1000 $finish();
  end
`endif
endmodule
