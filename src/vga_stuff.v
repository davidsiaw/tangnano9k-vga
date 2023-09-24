module VgaStuff(
  input wire clk,
  output wire [10:0] pixelx,
  output wire [10:0] pixely,
  output wire hsync,
  output wire vsync,
);

reg [10:0] hcnt = 0;
reg [10:0] vcnt = 0;
reg hsync_level = 1;
reg vsync_level = 1;
reg h_onscreen = 0;
reg v_onscreen = 0;

always @(posedge clk) begin
  hcnt <= hcnt + 1;

  // on screen signal
  if (hcnt == 0) begin
    h_onscreen <= 1;
  end

  if (hcnt == 640) begin
    h_onscreen <= 0;
  end

  if (vcnt == 0) begin
    v_onscreen <= 1;
  end

  if (vcnt == 480) begin
    v_onscreen <= 0;
  end

  // hsync is active low
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

  // vsync is active low too
  if (vcnt == 490) begin
    vsync_level <= 0;
  end

  if (vcnt == 492) begin
    vsync_level <= 1;
  end

  if (vcnt == 525) begin
    vcnt <= 0;
  end
end

assign hsync = hsync_level;
assign vsync = vsync_level;

wire onscreen;
assign onscreen = h_onscreen & v_onscreen;

assign pixelx = {11{onscreen}} & hcnt;
assign pixely = {11{onscreen}} & vcnt;

endmodule

