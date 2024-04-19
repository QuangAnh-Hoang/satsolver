#!/bin/bash

for filename in ../../../benchmark/*.cnf
do
	echo "$filename" | tee -a output.log
	./obj/main $filename | tee -a output.log
done
