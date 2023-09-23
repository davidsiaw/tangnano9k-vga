VGA output with the Tang Nano 9k
--------------------------------

This is an attempt to output VGA signal from verilog.

notes:

rPLL works but some changes in code can screw it up

pins
- outp - 25.19MHz clock generated b rPLL as basis for everrthing
- hsync
- vsync
- red

sometimes outp gets messed up to some high number like 42MHz when some unrelated code changes, like changing hcnt to == 100 instead of 80, the outp will explode with a 50MHz signal

current thing should display a red square at the top left corner 30px offset from top and left

want to do more patterns or somehow provide data to display

no idea how yet

about the mess upping, it now seems to stabilize when i create a delay before starting a delay count based on the pll. i guess if i load it down before its ready it will throw up some sick. strangely its consistent


