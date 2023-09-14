run: hello
	python3 run.py

hello: hello.rpl
	rtppl --release $<

clean:
	rm -f a a-in1 a-out1 a-co* b b-in1 b-out1 b-co* config.task* network.json
