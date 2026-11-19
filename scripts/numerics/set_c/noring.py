import re,sys
log,lean=sys.argv[1],sys.argv[2]
L=open(lean).read().split('\n')
s=set(eval(open('noring.txt').read())) if __import__('os').path.exists('noring.txt') else set()
for m in re.finditer(r'SetC\w+\.lean:(\d+):\d+: No goals',open(log).read()):
    ln=int(m.group(1))-1
    k=ln
    while not L[k].startswith('theorem'): k-=1
    nm=L[k].split()[1]; p,i=nm.split('_e'); s.add((p,int(i)))
open('noring.txt','w').write(repr(sorted(s)))
print(sorted(s))
