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

localparam WAIT_TIME = 1048768 * 10;
reg [5:0] ledCounter = 0;
reg [31:0] clockCounter = 0;

Clk25MHz clk25(
  .in_clk(in_clk),
  .out_clk(clk)
);

always @(posedge clk) begin
    clockCounter <= clockCounter + 1;
    if (clockCounter == WAIT_TIME) begin
        clockCounter <= 0;
        ledCounter <= ledCounter + 1;
    end
end

`ifdef FORMAL
  assume property (clockCounter != 0);
  assert property (clockCounter != 1);
`endif

assign led = ~ledCounter;
assign outp = clk;

wire h_clk;
assign h_clk = clk; // make sure a lock is achieved.

reg [10:0] hcnt = 0;
reg [10:0] vcnt = 0;
reg hsync_level = 1;
reg vsync_level = 1;
reg red_level = 0;

reg cc = 0;
reg dd = 0;

// h_clk can be seen on output.
always @(posedge h_clk) begin
  // send hsync signal
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

  // send vsync signal
  if (vcnt == 490) begin
    vsync_level <= 0;
  end

  if (vcnt == 492) begin
    vsync_level <= 1;
  end

  if (vcnt == 525) begin
     vcnt <= 0;
  end
  
  // draw checkeboard pattern
  cc <= vcnt[4];
  dd <= hcnt[4];
  
  red_level <= cc ^ dd;
end


assign hsync = hsync_level;
assign vsync = vsync_level;
assign red = red_level;


endmodule
