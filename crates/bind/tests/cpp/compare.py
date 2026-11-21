import sys, collections
def recs(p):
    r=collections.OrderedDict(); cur=None
    for l in open(p, encoding='utf-8', errors='replace'):
        l=l.rstrip('\n')
        if l.startswith('# '): cur=l; r[cur]=[]
        elif cur: r[cur].append(l)
        else: r.setdefault('_pre',[]).append(l)
    return r
a=recs(sys.argv[1]); b=recs(sys.argv[2])
kinds=collections.Counter(); ex={}
bad=0
for k in a:
    if a[k]!=b.get(k):
        bad+=1
        for x,y in zip(a[k],b.get(k,[])):
            if x!=y:
                key=x.split(' ')[0].split('(')[0]
                kinds[key]+=1
                ex.setdefault(key,[]).append((k,x,y))
print('records',len(a),'differing',bad)
for k,n in kinds.most_common(): 
    print(n,k)
    for e in ex[k][:int(sys.argv[3]) if len(sys.argv)>3 else 2]: print('   ',e[0],'\n      ada  :',e[1],'\n      vbind:',e[2])
