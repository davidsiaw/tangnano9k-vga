module top
(
    input wire in_clk,
    output wire [5:0] led,
    output wire outp,
    output wire hsync,
    output wire vsync,
    output wire red
);

wire clk;
wire clk_ready;
wire [10:0] pixelx;
wire [10:0] pixely;

Clk25MHz clk25(
  .in_clk(in_clk),
  .out_clk(clk),
  .clk_ready(clk_ready)
);

VgaStuff vga(
  .rst(~clk_ready),
  .clk(clk),
  .pixelx(pixelx),
  .pixely(pixely),
  .hsync(hsync),
  .vsync(vsync)
);

// unused atm
wire green;
wire blue;

DisplayOutput out(
  .rst(~clk_ready),
  .clk(clk),
  .pixelx(pixelx),
  .pixely(pixely),
  .r(red),
  .g(green),
  .b(blue)
);

assign led = {6{1'b1}};
assign outp = clk;
// assign red = pixelx[4] ^ pixely[4];

endmodule

