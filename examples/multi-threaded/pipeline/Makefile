all: pipeline_test pipeline_test_orig

pipeline_test: pipeline_test.c
	ivycc -Wall --sharc --heapsafe --deputy --sc-infer-sharing=$$PWD -include hslib.h -g -o $@ pipeline_test.c

pipeline_test_orig: pipeline_test_orig.c
	gcc -Wall -o $@ pipeline_test_orig.c -lpthread

clean:
	-killall ivy.asm.exe
	rm -f *.cil.c *.i pipeline_test pipeline_test_orig outFile.txt
	rm -rf sharc.log .ppatches demo/*.i demo/*.cil.c demo/p? demo/.ppatches
