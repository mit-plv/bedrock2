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
  input wire [3:0] write_byte_enable,
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
      if (write_byte_enable[0]) begin
        byte0[addr_[0]] <= write_[0];
      end;
      if (write_byte_enable[1]) begin
        byte1[addr_[1]] <= write_[1];
      end;
      if (write_byte_enable[2]) begin
        byte2[addr_[2]] <= write_[2];
      end;
      if (write_byte_enable[3]) begin
        byte3[addr_[3]] <= write_[3];
      end
    end
  end
endmodule

module system(
`ifdef SYNTHESIS
  input wire clk,
  input wire spi_miso,
`endif
  output reg [7:0] led = 8'hff,
  output reg spi_clk = 0,
  output wire spi_mosi,
  output reg spi_csn = 1,
  output reg lightbulb = 0
);

`ifndef SYNTHESIS
  reg clk=0;
  wire spi_miso; assign spi_miso = spi_mosi;
`endif

  reg resetn = 1'b0; always @(posedge clk) begin resetn <= 1'b1; end

  parameter integer LGSZW = 13;
  wire [31:0] ram_read;
  wire [68:0] obtain_rq_get;
  wire rdy_obtain_rq_get;
  wire en_obtain_rq_get = rdy_obtain_rq_get;
  wire rdy_send_rs_put;
  wire [31:0] mem_rq_data = obtain_rq_get[31:0];
  wire [3:0] mem_write_byte_enable = obtain_rq_get[35:32];
  wire mem_rq_iswrite = obtain_rq_get[36];
  wire [31:0] mem_rq_addr = obtain_rq_get[68:37];
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
    .write_byte_enable(mem_write_byte_enable),
    .write(mem_rq_data),
    .rq_en(en_obtain_rq_get && rdy_obtain_rq_get && rq_addr_is_bram),
    .rs_en(ram_rs_en),
    .read(ram_read)
  );

  assign instant_rs_en = en_obtain_rq_get && (mem_rq_addr == 32'h10012008 || mem_rq_addr == 32'h1001200c || mem_rq_addr == 32'h10024018 || mem_rq_addr == 32'h10024048 || mem_rq_addr == 32'h1002404c || mem_rq_addr == 32'h10012038);
  assign instant_rs =
	  (!instant_rs_en) ? 32'hxxxxxxxx
	  : (mem_rq_addr == 32'h1001200c && !mem_rq_iswrite) ? {8'h00, led, 16'h0000}
	  : (mem_rq_addr == 32'h10024048 && !mem_rq_iswrite) ? {(!spi_tx_rdy), 31'h0}
	  : (mem_rq_addr == 32'h1002404c && !mem_rq_iswrite) ? {(!spi_tx_rdy), 23'h0, spi_rx_buf}
    : mem_rq_addr == 32'h10012038 ? 0
	  : 32'hxxxxxxxx;
  wire spi_tx_en = en_obtain_rq_get && mem_rq_iswrite && mem_rq_addr == 32'h10024048;
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
      spi_rx_buf = {spi_rx_buf[6:0], spi_miso};
    end else if (spi_clk) begin
      spi_clk <= 0;
      spi_tx_buf <= {spi_tx_buf[6:0], 1'bx};
      spi_tx_remaining <= spi_tx_remaining - 1;
    end
  end
  wire spi_setcs_en = en_obtain_rq_get && mem_rq_iswrite && mem_rq_addr == 32'h10024018;
  always @(posedge clk) begin
    if (spi_setcs_en) begin
        spi_csn <= !mem_rq_data[1];
    end
  end

  reg [5:0] cnt = 0;
  always @(posedge clk) begin
    led[6] <= 0;
    led [5:0] <= ~cnt;
    if (en_obtain_rq_get && mem_rq_iswrite && mem_rq_addr == 32'h1001200c) begin
      lightbulb <= mem_rq_data[23];
      led[7] <= !mem_rq_data[23];
      cnt <= cnt + 1;
    end
  end

`ifndef SYNTHESIS
  always #1 clk = !clk;
  initial begin
    $dumpfile("system.vcd");
    $dumpvars(1,
              mkTop.proc_m13_lastPc,
              mkTop.proc_m13_stall,
              mkTop.WILL_FIRE_RL_proc_m10_instFetchRq,
              mkTop.WILL_FIRE_RL_proc_m10_instFetchRs,
              mkTop.WILL_FIRE_RL_proc_m10_instFetchRsIgnore,
              mkTop.WILL_FIRE_RL_proc_m10_modifyPc,
              mkTop.WILL_FIRE_RL_proc_m10_pgmInitRq,
              mkTop.WILL_FIRE_RL_proc_m10_pgmInitRqEnd,
              mkTop.WILL_FIRE_RL_proc_m10_pgmInitRs,
              mkTop.WILL_FIRE_RL_proc_m10_pgmInitRsEnd,
              mkTop.WILL_FIRE_RL_proc_m11_decodeLd,
              mkTop.WILL_FIRE_RL_proc_m11_decodeNm,
              mkTop.WILL_FIRE_RL_proc_m11_decodeSt,
              mkTop.WILL_FIRE_RL_proc_m12_execBypass,
              mkTop.WILL_FIRE_RL_proc_m12_execNm,
              mkTop.WILL_FIRE_RL_proc_m13_repLd,
              mkTop.WILL_FIRE_RL_proc_m13_repLdZ,
              mkTop.WILL_FIRE_RL_proc_m13_repSt,
              mkTop.WILL_FIRE_RL_proc_m13_reqLd,
              mkTop.WILL_FIRE_RL_proc_m13_reqSt,
              mkTop.WILL_FIRE_RL_proc_m13_wbNm,
              mkTop.WILL_FIRE_RL_proc_m13_wbNmZ,
              mkTop.WILL_FIRE_RL_proc_m13_wrongEpoch,
              led, spi_clk, spi_csn, spi_mosi, spi_miso, clk, resetn,
              rdy_obtain_rq_get, en_obtain_rq_get, rq_addr_is_bram, mem_rq_addr, mem_rq_data,
              mem_write_byte_enable, mem_rq_iswrite,
              ram_rs_en, ram_read, instant_rs_en, instant_rs, rdy_send_rs_put,
              spi_tx_buf, spi_rx_buf, spi_tx_rdy);
    #90000 $finish();
  end
`endif
endmodule
