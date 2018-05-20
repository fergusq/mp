#!/bin/bash
	for test in 1 2 3; do
		
		../bin/mp "arrays/$test.pas" >tmp.c
		gcc tmp.c -o etmp && ./etmp >tmp.out
		
		if cmp --silent tmp.out "arrays/$test.out"; then
			echo "Test $test: OK"
		else
			echo "Test $test: failed"
			diff "arrays/$test.out" tmp.out
		fi
	done
	