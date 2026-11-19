import re,sys
f=sys.argv[1]; out=open(sys.argv[2]).read()
lines=open(f).read().split('\n')
ws=sorted({(int(a),int(b)) for a,b in re.findall(r':(\d+):(\d+): warning: This simp argument is unused',out)},reverse=True)
for ln,col in ws:
    s=lines[ln-1]
    m=re.match(r'[^\s,\]]+',s[col:])
    tok=m.group(0)
    end=col+len(tok)
    if s[end:end+2]==', ': s=s[:col]+s[end+2:]
    elif s[col-2:col]==', ': s=s[:col-2]+s[end:]
    else: s=s[:col]+s[end:]
    lines[ln-1]=s
open(f,'w').write('\n'.join(lines))
print(len(ws))
