#!/bin/bash
	for test in 1 2 3; do
		
		../bin/mp "functions/$test.pas" >tmp.c
		gcc tmp.c -o etmp && ./etmp >tmp.out
		
		if cmp --silent tmp.out "functions/$test.out"; then
			echo "Test $test: OK"
		else
			echo "Test $test: failed"
			diff "functions/$test.out" tmp.out
		fi
	done
	