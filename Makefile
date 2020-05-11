.PHONY: build clean-build

all: build run

run: build
	docker run -ti tornado

interactive: build
	docker run -ti tornado /bin/bash

build:
	docker build									\
		 --tag=tornado								\
		 .

clean-build:
	docker build									\
		 --tag=tornado								\
		 --no-cache								\
		 .
