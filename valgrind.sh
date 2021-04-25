g++ -O0 -o main.out main.cpp 
valgrind --tool=callgrind --callgrind-out-file=./callgrind.out ./main.out < tools/in/0000.txt > tools/out/0.txt
gprof2dot -f callgrind ./callgrind.out | dot -Tsvg -o report.svg
explorer.exe report.svg