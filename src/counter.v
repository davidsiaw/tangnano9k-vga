module counter
(
    input in_clk,
    output [5:0] led,
    output outp,
    output hsync,
    output vsync,
    output red
);

wire clk;

Clk25MHz clk25(
  .in_clk(in_clk),
  .out_clk(clk)
);

wire [10:0] pixelx;
wire [10:0] pixely;

VgaStuff vga(
  .clk(clk),
  .pixelx(pixelx),
  .pixely(pixely),
  .hsync(hsync),
  .vsync(vsync)

);

// checkerboard pattern
assign red = pixelx[4] ^ pixely[4];
assign outp = clk;
assign led = {6{1'b1}};

endmodule

