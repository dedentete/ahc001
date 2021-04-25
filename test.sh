n=$(($1-1))
g++ -o main.out main.cpp 
cd tools
for i in `seq 0 $n`
do
    if [ $(($i%8)) -eq 0 ]; then
        wait
    fi
    t=$(printf "%04d" $i)
    ../main.out < in/$t.txt > out/$i.txt &
done
wait
for i in `seq 0 $n`
do
    t=$(printf "%04d" $i)
    if [ $i = 0 ]; then
        cargo run --release --bin vis in/$t.txt out/$i.txt > scores.txt
    else 
        cargo run --release --bin vis in/$t.txt out/$i.txt >> scores.txt
    fi
done
for num in `cat scores.txt`
do
    sum=`expr $sum + $num`
done
echo $sum
