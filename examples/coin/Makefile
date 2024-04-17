run: cf
	python3 run.py

cf: coin.rpl
	rtppl $<

clean:
	rm -rf cf cf-in1 bias cf.collect config.task* network.json __pycache__
