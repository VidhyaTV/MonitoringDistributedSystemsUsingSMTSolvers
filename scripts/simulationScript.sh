#!/bin/bash

exe=./wcp

#epsilons=(10 20 50 100 1000 10000)
epsilons=(1000)
nprocs=(10)
lpr=(0.01)
#lpr=(0.1 0.05 0.02 0.01 0.001)
deltas=(100)
#deltas=(10 20 50 100 1000)
alphas=(0.01)
#alphas=(0.1 0.05 0.02 0.01 0.001)
interval=(10)
#interval=(1 2 5 10 100)
hundred=100

make clean
make

for e in "${epsilons[@]}"
#for e in {1..100000..5}
do
	for p in "${nprocs[@]}"
	#for p in {1..50..1}
	do
		for l in "${lpr[@]}"
		do
			for a in "${alphas[@]}"
			#for a in {1..100..1}
			do
				for d in "${deltas[@]}"
				do
					for v in "${interval[@]}"
					#for v in {1..100..1}
					do
					#${exe} -e${e} -p${p} -l${l} -d${d} -a$(echo "scale=2;$a/$hundred"|bc) -u1000 -mRandom -b20 -r1 -tCompleteGraph -v${v}
					${exe} -e${e} -p${p} -l${l} -d${d} -a${a} -u100000 -mRandom -b20 -r3 -tCompleteGraph -v${v}
					echo
					echo "---------------------"
					echo
					done
				done
			done
		done
	done  
done
