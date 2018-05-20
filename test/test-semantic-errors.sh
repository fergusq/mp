#!/bin/bash
	for test in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24; do
		
		../bin/mp "semantic-errors/$test.pas" >/dev/null 2>tmp.out
                
		if cmp --silent tmp.out "semantic-errors/$test.out"; then
			echo "Test $test: OK"
		else
			echo "Test $test: failed"
			diff "semantic-errors/$test.out" tmp.out
		fi
	done
	