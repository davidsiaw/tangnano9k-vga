
module rPLL (CLKOUT, CLKOUTP, CLKOUTD, CLKOUTD3, LOCK, CLKIN, CLKFB, FBDSEL, IDSEL, ODSEL, DUTYDA, PSDA, FDLY, RESET, RESET_P);
input CLKIN;
input CLKFB;
input RESET;
input RESET_P;
input [5:0] FBDSEL;
input [5:0] IDSEL;
input [5:0] ODSEL;
input [3:0] PSDA,FDLY;
input [3:0] DUTYDA;

output CLKOUT;
output LOCK;
output CLKOUTP;
output CLKOUTD;
output CLKOUTD3;

parameter FCLKIN = "100.0";         // frequency of CLKIN
parameter DYN_IDIV_SEL= "false";    // true:IDSEL, false:IDIV_SEL
parameter IDIV_SEL = 0;             // 0:1, 1:2 ... 63:64
parameter DYN_FBDIV_SEL= "false";   // true:FBDSEL, false:FBDIV_SEL
parameter FBDIV_SEL = 0;            // 0:1, 1:2 ... 63:64
parameter DYN_ODIV_SEL= "false";    // true:ODSEL, false:ODIV_SEL
parameter ODIV_SEL = 8;             // 2/4/8/16/32/48/64/80/96/112/128

parameter PSDA_SEL= "0000";
parameter DYN_DA_EN = "false";      // true:PSDA or DUTYDA or FDA, false: DA_SEL
parameter DUTYDA_SEL= "1000";

parameter CLKOUT_FT_DIR = 1'b1;     // CLKOUT fine tuning direction. 1'b1 only
parameter CLKOUTP_FT_DIR = 1'b1;    // 1'b1 only
parameter CLKOUT_DLY_STEP = 0;      // 0, 1, 2, 4
parameter CLKOUTP_DLY_STEP = 0;     // 0, 1, 2

parameter CLKFB_SEL = "internal";   // "internal", "external"
parameter CLKOUT_BYPASS = "false";  // "true", "false"
parameter CLKOUTP_BYPASS = "false"; // "true", "false"
parameter CLKOUTD_BYPASS = "false"; // "true", "false"
parameter DYN_SDIV_SEL = 2;         // 2~128, only even numbers
parameter CLKOUTD_SRC =  "CLKOUT";  // CLKOUT, CLKOUTP
parameter CLKOUTD3_SRC = "CLKOUT";  // CLKOUT, CLKOUTP
parameter DEVICE = "GW1N-1";        // "GW1N-1", "GW1N-4", "GW1N-9", "GW1NR-4", "GW1NR-9", "GW1N-4B", "GW1NR-4B", "GW1NS-2", "GW1NS-2C", "GW1NZ-1", "GW1NSR-2", "GW1NSR-2C", "GW1N-1S", "GW1NSE-2C", "GW1NRF-4B", "GW1N-9C", "GW1NR-9C", "GW1N-4C", "GW1NR-4C"

endmodule


(* blackbox *)
module OSC(OSCOUT);
output OSCOUT;

parameter FREQ_DIV = 128;
parameter DEVICE = "GW1N-9";
endmodule


module counter
(
    input in_clk,
    output [5:0] led,
    output outp,
    output hsync,
    output vsync,
    output red
);

wire osc_clk;
wire clk;
wire clk_lock;

OSC osc(
	.OSCOUT(osc_clk)
);
defparam osc.FREQ_DIV=4;

// https://juj.github.io/gowin_fpga_code_generators/pll_calculator.html
// make sure you test your pll output on a real device before committing
// certain frequencies can be very unstable and constantly loses clock lock
 rPLL #( // For GW1NR-9C C6/I5 (Tang Nano 9K proto dev board)
  .FCLKIN("27"),
  .IDIV_SEL(2), // -> PFD = 9 MHz (range: 3-400 MHz)
  .FBDIV_SEL(27), // -> CLKOUT = 252 MHz (range: 3.125-600 MHz)
  .ODIV_SEL(2) // -> VCO = 504 MHz (range: 400-1200 MHz)
) pll (.CLKOUTP(), .CLKOUTD(), .CLKOUTD3(), .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0), .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0), .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
  .CLKIN(in_clk), // 27 MHz
  .CLKOUT(clk), // 252 MHz
  .LOCK(clk_lock)
);

localparam WAIT_TIME = 1048768 ;
reg [5:0] ledCounter = 0;
reg [26:0] clockCounter = 0;
reg a = 0;
reg [7:0] ccount = 0;


always @(posedge clk) begin
    clockCounter <= clockCounter + 1;
    if (clockCounter == WAIT_TIME) begin
        clockCounter <= 0;
        ledCounter <= ledCounter + 1;
    end

    ccount <= ccount + 1;

    if(ccount == 4) begin
      if (a == 1) begin
          a <= 0;
      end
      else begin
          a <= 1;
      end
      ccount <= 0;
    end
end

`ifdef FORMAL
  assume property (clockCounter != 0);
  assert property (clockCounter != 1);
`endif

assign led = ~ledCounter;
assign outp = a;

wire h_clk;
assign h_clk = a & clk_lock;

reg [10:0] hcnt = 0;
reg [10:0] vcnt = 0;
reg hsync_level = 1;
reg vsync_level = 1;
reg red_level = 0;

reg cc = 0;

always @(posedge h_clk) begin
  hcnt <= hcnt + 1;

  if (hcnt == 656) begin
    hsync_level <= 0;
  end
  
  if (hcnt == 752) begin
    hsync_level <= 1;
  end

  if (hcnt == 800) begin
    hcnt <= 0;
    vcnt <= vcnt + 1;
  end

  if (vcnt == 490) begin
    vsync_level <= 0;
  end

  if (vcnt == 492) begin
    vsync_level <= 1;
  end

  if (vcnt == 525) begin
     vcnt <= 0;
  end

  if (vcnt == 30) begin
    cc <= 1;
  end

  if (vcnt == 80) begin
    cc <= 0;
  end
  
  if (hcnt == 30) begin
    red_level <= 1 & cc;
  end

  if (hcnt == 80) begin
    red_level <= 0;
  end
  

end


assign hsync = hsync_level;
assign vsync = vsync_level;
assign red = red_level;


endmodule
