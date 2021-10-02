kv.exe: kv.c
	gcc -Wall $< -o $@

kv.run: kv.exe
	./$< 1234

kv.test: kv.exe
	./$< 1234 & { \
		echo PUT abcd 1234 | nc 127.0.0.1 1234; \
		echo PUT wxyz 5678 | nc 127.0.0.1 1234; \
		echo GET abcd      | nc 127.0.0.1 1234; \
		echo GET wxyz      | nc 127.0.0.1 1234; \
		echo GET aaaa      | nc 127.0.0.1 1234; }
