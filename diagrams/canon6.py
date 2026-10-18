import itertools, json, sys, time, numpy as np
sys.path.insert(0, '.')
import labelled_io
pairs, diags = labelled_io.load('n6_labelled.txt')
n=6; m=len(pairs)
pos={}
for i,(a,b) in enumerate(pairs): pos[(a,b)]=pos[(b,a)]=i
N=len(diags)
E=np.array([d[0] for d in diags], dtype=np.int64)           # N x 15
CZ=np.array([[ (d[1]>>k)&1 for k in range(n)] for d in diags], dtype=np.int64)
CW=np.array([[ (d[2]>>k)&1 for k in range(n)] for d in diags], dtype=np.int64)
sw=np.array([0,2,1,3],dtype=np.int64)
w4=4**np.arange(m,dtype=np.int64)[::-1]       # most significant digit = position 0
w2=2**np.arange(n,dtype=np.int64)[::-1]
def key(Ev, Cz, Cw):
    return ((Ev*w4).sum(1) << 12) + ((Cz*w2).sum(1) << 6) + (Cw*w2).sum(1)
best=None; t=time.time()
for p in itertools.permutations(range(n)):
    # body k -> p[k]; new position of pair i=(a,b) is pos[(p[a],p[b])]; new vector nv[pos(..)] = v[i]
    idx=np.empty(m,dtype=np.int64)
    for i,(a,b) in enumerate(pairs): idx[pos[(p[a],p[b])]]=i
    pinv=np.empty(n,dtype=np.int64)
    for k in range(n): pinv[p[k]]=k
    Ev=E[:,idx]; Cz=CZ[:,pinv]; Cw=CW[:,pinv]
    k1=key(Ev,Cz,Cw); k2=key(sw[Ev],Cw,Cz)
    kk=np.minimum(k1,k2)
    best=kk if best is None else np.minimum(best,kk)
print('canonicalized in %.1f s'%(time.time()-t))
cls,counts=np.unique(best,return_counts=True)
print(len(cls),'classes under S6 x colour exchange')
# decode representatives
reps=[]
for c,cnt in zip(cls.tolist(),counts.tolist()):
    cw=c & 63; cz=(c>>6)&63; ev=c>>12
    v=[]
    for i in range(m):
        v.append((ev // (4**(m-1-i)))%4)
    reps.append({'edges':{f'{a}{b}':v[i] for i,(a,b) in enumerate(pairs) if v[i]},
                 'zcircles':[k for k in range(n) if (cz>>(n-1-k))&1],
                 'wcircles':[k for k in range(n) if (cw>>(n-1-k))&1],'labelled':cnt})
json.dump({'n':6,'labelled':N,'classes':reps},open('n6.json','w'),indent=1)
print('wrote n6.json')
