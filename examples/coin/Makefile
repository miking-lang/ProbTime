run: cf
	python3 run.py

cf: coin.rpl
	rtppl --release $<

clean:
	rm -f cf cf-in1 cf-out1 cf-co* config.task* network.json
