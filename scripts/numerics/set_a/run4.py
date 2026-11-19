import sys
sys.argv=[sys.argv[0]]+sys.argv[2:]
exec(open('fit4.py').read())
tname=sys.argv[0]
