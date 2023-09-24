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

reg [10:0] x0 = 50;
reg [10:0] y0 = 50;
wire [10:0] x1;
wire [10:0] y1;

reg xd = 1;
reg yd = 1;

assign x1 = 100;
assign y1 = 100;


reg [10:0] hcount = 0;
reg [10:0] vcount = 0;
reg x_in = 0;
reg y_in = 0;

always @(posedge clk) begin
  if (pixelx == x0) begin
    x_in <= 1;
    hcount <= 0;

    if (pixely == y0) begin
      y_in <= 1;
      vcount <= 0;
    end

    if (y_in == 1) begin
      vcount <= vcount + 1;
    end

    if (vcount == y1) begin
      y_in <= 0;
    end
  end

  if (x_in == 1) begin
    hcount <= hcount + 1;
  end

  if (hcount == x1) begin
    x_in <= 0;
  end

end


assign red = x_in & y_in;



assign outp = clk;
assign led = ~{1'b1, 1'b1, 1'b1, 1'b1, 1'b1, y_in};


always @(posedge vsync) begin
  if (xd == 0) begin
    x0 <= x0 - 1;
  end
  else begin
    x0 <= x0 + 1;
  end

  if (yd == 0) begin
    y0 <= y0 - 1;
  end
  else begin
    y0 <= y0 + 1;
  end

  if (x0 == 0) begin
    xd <= 1;
  end

  if (x0 == 540) begin
    xd <= 0;
  end

  if (y0 == 0) begin
    yd <= 1;
  end

  if (y0 == 380) begin
    yd <= 0;
  end

end

endmodule

