module Clk25MHz(
  input in_clk,
  output out_clk
);

// tells us if the PLL has stabilized
wire clk_lock;

wire osc_clk;

// use the rPLL to generate clock close to a multiple
// of 2x the clock we want.
wire fclk;

// actual clock. But we only use it after clk_lock is high
wire clk;

OSC osc(
	.OSCOUT(osc_clk)
);
defparam osc.FREQ_DIV=4;

// https://juj.github.io/gowin_fpga_code_generators/pll_calculator.html
rPLL #( // For GW1NR-9C C6/I5 (Tang Nano 9K proto dev board)
  .FCLKIN("27"),
  .IDIV_SEL(2), // -> PFD = 9 MHz (range: 3-400 MHz)
  .FBDIV_SEL(27), // -> CLKOUT = 252 MHz (range: 3.125-600 MHz)
  .DYN_SDIV_SEL(10),   .ODIV_SEL(4) // -> VCO = 1008 MHz (range: 400-1200 MHz)
) pll (.CLKOUTP(), .CLKOUTD3(), .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0), .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0), .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
  .CLKIN(in_clk), // 27 MHz
  .CLKOUT(fclk), // 252 MHz
  .CLKOUTD(clk), // 25.2 MHz
  .LOCK(clk_lock)
);

assign out_clk = clk & clk_lock;

endmodule

