module VgaStuff(
  input wire rst,
  input wire clk,
  output wire [10:0] pixelx,
  output wire [10:0] pixely,
  output wire hsync,
  output wire vsync
);

reg [10:0] c_hcnt;
reg [10:0] c_vcnt;
reg c_hsync_level;
reg c_vsync_level;
reg c_h_onscreen;
reg c_v_onscreen;
reg c_onscreen;
reg [10:0] c_pixelx;
reg [10:0] c_pixely;

always_comb begin
  if (rst) begin
    c_hcnt <= 0;
    c_vcnt <= 0;
    c_hsync_level <= 1;
    c_vsync_level <= 1;
    c_h_onscreen <= 0;
    c_v_onscreen <= 0;
    c_onscreen = 0;
    c_pixelx = 0;
    c_pixely = 0;
  end

  c_hcnt <= r_hcnt + 1;

  // on screen signal
  if (r_hcnt == 0) begin
    c_h_onscreen <= 1;
  end
  else if (r_hcnt == 640) begin
    c_h_onscreen <= 0;
  end
  else begin
    c_h_onscreen <= r_h_onscreen;
  end

  if (r_vcnt == 0) begin
    c_v_onscreen <= 1;
  end
  else if (r_vcnt == 480) begin
    c_v_onscreen <= 0;
  end
  else begin
    c_v_onscreen <= r_v_onscreen;
  end

  // hsync is active low
  if (r_hcnt == 656) begin
    c_hsync_level <= 0;
  end
  else if (r_hcnt == 752) begin
    c_hsync_level <= 1;
  end
  else begin
    c_hsync_level <= r_hsync_level;
  end

  if (r_hcnt == 800) begin
    c_hcnt <= 0;
    c_vcnt <= r_vcnt + 1;
  end
  else begin
    c_vcnt <= r_vcnt;
  end

  // vsync is active low too
  if (r_vcnt == 490) begin
    c_vsync_level <= 0;
  end
  else if (r_vcnt == 492) begin
    c_vsync_level <= 1;
  end
  else begin
    c_vsync_level <= r_vsync_level;
  end

  if (r_vcnt == 525) begin
    c_vcnt <= 0;
  end

  c_onscreen <= r_v_onscreen & r_h_onscreen;

  c_pixelx <= {11{r_onscreen}} & r_hcnt;
  c_pixely <= {11{r_onscreen}} & r_vcnt;
end


reg [10:0] r_hcnt;
reg [10:0] r_vcnt;
reg r_hsync_level;
reg r_vsync_level;
reg r_h_onscreen;
reg r_v_onscreen;
reg r_onscreen;
reg [10:0] r_pixelx;
reg [10:0] r_pixely;

always_ff @(posedge clk) begin
  r_hcnt <= c_hcnt;
  r_vcnt <= c_vcnt;
  r_hsync_level <= c_hsync_level;
  r_vsync_level <= c_vsync_level;
  r_h_onscreen <= c_h_onscreen;
  r_v_onscreen <= c_v_onscreen;
  r_onscreen <= c_onscreen;
  r_pixelx <= c_pixelx;
  r_pixely <= c_pixely;
end

assign hsync = r_hsync_level;
assign vsync = r_vsync_level;

assign pixelx = r_pixelx;
assign pixely = r_pixely;

endmodule

