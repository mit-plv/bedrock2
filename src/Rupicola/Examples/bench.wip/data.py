with open("data.h", mode="wb") as f:
    nums = bytes(int(s.strip()) for s in open("data.txt"))
    f.write(b'char data[] = "{}";'.format(nums.encode("")))
