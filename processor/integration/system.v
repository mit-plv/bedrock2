
`default_nettype none
`define assert(condition) if(!((|{condition})===1)) begin $display("FAIL"); $finish(1); end

module testbench; 
    reg clock=0, reset=1;
    reg [31:0] program [0:31];

    reg en_obtain_rq_get = 0;
    wire [64:0] obtain_rq_get;
    wire rdy_obtain_rq_get;
    reg en_send_rs_put = 0;
    reg [31:0] send_rs_put = 0;
    wire rdy_send_rs_put;
    mkTop mkTop(.CLK(clock),
                .RST_N(~reset),
                .EN_obtain_rq_get(en_obtain_rq_get),
                .obtain_rq_get(obtain_rq_get),
                .RDY_obtain_rq_get(rdy_obtain_rq_get),

                .send_rs_put(send_rs_put),
                .EN_send_rs_put(en_send_rs_put),
                .RDY_send_rs_put(rdy_send_rs_put)
              );
    wire A = obtain_rq_get[0];
    wire [31:0] B = obtain_rq_get[32:1];
    wire [31:0] C = obtain_rq_get[64:33];

    always @(posedge clock) begin
      if (rdy_obtain_rq_get && rdy_send_rs_put) begin
        if ((C>>2) < 32) begin
          en_obtain_rq_get <= 1;
          send_rs_put <= program[C >> 2];
          en_send_rs_put <= 1;
        end else begin
          en_obtain_rq_get <= 1;
          send_rs_put <= C;
          en_send_rs_put <= 1;
        end
      end else begin
        if (en_obtain_rq_get) begin
          en_obtain_rq_get <= 0;
        end
        if (en_send_rs_put) begin
          en_send_rs_put <= 0;
        end
      end
    end

    always #1 clock = !clock;
    initial begin 
      $readmemh("program.hex", program);
      $dumpfile("system.vcd");
      $dumpvars(1, clock, reset, en_obtain_rq_get, A, B, C, rdy_obtain_rq_get, en_send_rs_put, send_rs_put, rdy_send_rs_put);
      #2 reset <= 0;
      #100 $finish();
    end 
endmodule
