list:
    @just --list

build file: && clean
    coqc -Q . Tego {{file}}.v

build-all: && clean
	for file in `ls *.v`; do coqc -Q . Tego "$file"; done
    
clean:
    rm -f *.glob
    rm -f *.vok
    rm -f *.vos
    rm -f .*.aux
