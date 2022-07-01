for i in `seq 5 5 50`
do
	for j in `seq 10 10 100`
	do
		echo "size $i, prob $j"
		python3 gen_graphs.py $i $j > ../instances/benchmark_instances/graphs/random_${i}_${j}.lp
		(echo "#program normal." && cat ../instances/benchmark_instances/graphs/random_${i}_${j}.lp) > ../instances/benchmark_instances/graphs_newground2_v2/random_${i}_${j}.lp
	done
done

for i in `seq 100 100 1200`
do
	for j in `seq 10 10 100`
	do
		echo "size $i, prob $j"
		python3 gen_graphs.py $i $j > ../instances/benchmark_instances/graphs/random_${i}_${j}.lp
		(echo "#program normal." && cat ../instances/benchmark_instances/graphs/random_${i}_${j}.lp) > ../instances/benchmark_instances/graphs_newground2_v2/random_${i}_${j}.lp
	done
done