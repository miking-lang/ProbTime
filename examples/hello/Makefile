run: hello
	python3 run.py

hello: hello.rpl
	rtppl $<

clean:
	rm -rf a b *.collect a-in1 b-in1 dst system.json __pycache__
