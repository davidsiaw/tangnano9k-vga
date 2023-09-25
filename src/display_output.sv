module DisplayOutput
(
  input wire rst,
  input wire clk,
  input wire [10:0] pixelx,
  input wire [10:0] pixely,
  output wire r, g, b
);

localparam RECT_WIDTH = 100;
localparam RECT_HEIGHT = 100;

reg [10:0] c_x0;
reg [10:0] c_y0;
reg c_r;
reg c_xd;
reg c_yd;

always_comb begin
  if (rst) begin
    c_x0 <= 50;
    c_y0 <= 50;
    c_r <= 0;
    c_xd <= 1;
    c_yd <= 1;
  end
  else begin


  // End of frame. reset all
  if (pixelx == 639 && pixely == 479) begin
    
    if (r_xd == 0) begin
      c_x0 <= r_x0 - 1;
    end
    else begin
      c_x0 <= r_x0 + 1;
    end

    if (r_yd == 0) begin
      c_y0 <= r_y0 - 1;
    end
    else begin
      c_y0 <= r_y0 + 1;
    end


    if (r_x0 == 0) begin
      c_xd <= 1;
    end
    else if (r_x0 == 540) begin
      c_xd <= 0;
    end
    else begin
      c_xd <= r_xd;
    end

    if (r_y0 == 0) begin
      c_yd <= 1;
    end
    else if (r_y0 == 380) begin
      c_yd <= 0;
    end
    else begin
      c_yd <= r_yd;
    end
  end
  else begin
    c_xd <= r_xd;
    c_yd <= r_yd;
    c_x0 <= r_x0;
    c_y0 <= r_y0;
  end

  c_r <= pixelx >= r_x0 && pixelx < (r_x0+RECT_WIDTH) &&
	  pixely >= r_y0 && pixely < (r_y0+RECT_HEIGHT)
	  ;
  end
end

reg [10:0] r_x0;
reg [10:0] r_y0;
reg r_r;
reg r_xd;
reg r_yd;

always_ff @(posedge clk) begin
  r_x0 <= c_x0;
  r_y0 <= c_y0;
  r_r <= c_r;
  r_xd <= c_xd;
  r_yd <= c_yd;
end

assign r = r_r;
assign g = 1'b0;
assign b = 1'b0;

endmodule

