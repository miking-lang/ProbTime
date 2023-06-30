run: cf
	python3 run.py

cf: coin.rpl
	rtppl $<

clean:
	rm -f cf cf-in1 cf-out1 network.json
