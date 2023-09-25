DOCKER_PREFIX=docker run --rm -v $(PWD):/src --workdir /src
DOCKER_IMAGE=davidsiaw/yosys-docker
CMD_PREFIX=$(DOCKER_PREFIX) $(DOCKER_IMAGE)
PRIV_PREFIX=$(DOCKER_PREFIX) --privileged -v /dev:/dev $(DOCKER_IMAGE)
FREQ := 27

YOSYS=$(CMD_PREFIX) yosys
NEXTPNR_GOWIN=$(CMD_PREFIX) nextpnr-gowin
GOWIN_PACK=$(CMD_PREFIX) gowin_pack
OPENFPGALOADER=$(PRIV_PREFIX) openFPGALoader
FORMAL=$(CMD_PREFIX) yosys-smtbmc
VERILOG_FILES=$(filter-out src/tb.v, $(wildcard src/*.sv))

READ_VERILOG_PARAMS:=-lib -sv -specify +/gowin/cells_sim.v

GOWIN_FPGA_CST=fpga/tangnano9k.cst

all: obj/test.json

obj/test.ys: $(VERILOG_FILES)
	mkdir -p obj
	rm -f $@
	echo "# this file is generated by the makefile" > $@
	for number in $^ ; do \
	    echo "read_verilog $(READ_VERILOG_PARAMS) $$number" >> $@ ; \
	done
	echo "hierarchy -check -top counter" >> $@
	echo "proc" >> $@
	echo "flatten" >> $@
	echo "clean -purge" >> $@

obj/formal.ys: $(VERILOG_FILES)
	mkdir -p obj
	rm -f $@
	echo "# this file is generated by the makefile" > $@
	for number in $^ ; do \
	  echo "read_verilog -formal -assume-asserts $(READ_VERILOG_PARAMS) $$number" >> $@ ; \
	done
	echo "prep -top counter -nordff" >> $@

obj/test.smt2: obj/formal.ys
	echo "write_smt2 -wires " $@ >> $<
	$(YOSYS) $< | tee obj/yosys-formal-build.log

formal: obj/test.smt2
	$(FORMAL) $< | tee $@
	$(FORMAL) -i $< | tee -a $@

obj/test.json: obj/test.ys
	echo "synth_gowin -json" $@ >> $<
	$(YOSYS) $< | tee obj/yosys.log

obj/gowin_pnr_test.json: obj/test.json $(GOWIN_FPGA_CST)
	$(NEXTPNR_GOWIN) --json $< --write $@ --device GW1NR-LV9QN88PC6/I5 --freq $(FREQ) --cst $(GOWIN_FPGA_CST) | tee obj/nextpnr_gowin.log

obj/gowin_pack.fs: obj/gowin_pnr_test.json
	$(GOWIN_PACK) -d GW1N-9C -o $@ $< | tee obj/gowin_pack.log

upload_gowin: obj/gowin_pack.fs
	$(OPENFPGALOADER) -b tangnano9k obj/gowin_pack.fs

gowin: obj/gowin_pack.fs

clean:
	rm -rf obj

.PHONY: clean gowin all
