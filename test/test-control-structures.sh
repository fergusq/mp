#!/bin/bash
	for test in 1 2 3 4; do
		
		../bin/mp "control-structures/$test.pas" >tmp.c
		gcc tmp.c -o etmp && ./etmp >tmp.out
		
		if cmp --silent tmp.out "control-structures/$test.out"; then
			echo "Test $test: OK"
		else
			echo "Test $test: failed"
			diff "control-structures/$test.out" tmp.out
		fi
	done
	