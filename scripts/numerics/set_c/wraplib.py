import re
def wrap(line, maxlen=100):
    if len(line)<=maxlen: return [line]
    ind=len(line)-len(line.lstrip())
    cont=' '*(ind+4)
    out=[]; cur=line
    first=True
    while len(cur)>maxlen:
        # find last break point (space before + - * ) or after '(' ) within limit
        cut=-1
        for mt in re.finditer(r' (?=[\+\-\*] )| (?=\()',cur[:maxlen]):
            if mt.start()>len(cur)-len(cur.lstrip())+8: cut=mt.start()
        if cut==-1:
            for mt in re.finditer(r' ',cur[:maxlen]):
                if mt.start()>len(cur)-len(cur.lstrip())+8: cut=mt.start()
        out.append(cur[:cut]); cur=cont+cur[cut+1:]
    out.append(cur)
    return out
