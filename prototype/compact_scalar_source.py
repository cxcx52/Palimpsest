"""Small explicit semantic example for the native Boolean-quadratic RoK.

One multiplication in F_p, not the archived 512-coefficient R_p multiplication.
The choice of a much smaller application is a scope tradeoff, not a claim that
the original application was compiled at the same cost. No end-to-end prover.
"""
from .relation_support import RingForms, verify_batch_labels, Row, negacyclic


class CompactScalarSource:
    p=2**51-165
    N=512
    width=51
    METADATA=(('session',4),('source_label',2),('sequence',1))

    def __init__(self,q):
        self.maximum_form=2**self.width-1
        self.integer_residual_bound=max(self.maximum_form**2,
                                       self.maximum_form*(self.p+1))
        if type(q) is not int or q<=max(self.integer_residual_bound,2**64):
            raise ValueError('q must exceed the full integer residual and metadata bounds')
        self.q=q;self.forms={'u':(0,1)};offset=1
        for name in ('x','y','E','h','slack_x','slack_y','slack_E'):
            self.forms[name]=(offset,self.width);offset+=self.width
        for field,words in self.METADATA:
            for word in range(words):
                self.forms[f'{field}[{word}]']=(offset,64);offset+=64
        self.witness_size=offset
        self.projection_names=('u','E')+tuple(f'{field}[{word}]'
                            for field,words in self.METADATA for word in range(words))

    def arithmetic_rows(self):
        for name in ('x','y','E'):
            yield Row('canonical_range',{'value':name},
                      ((1,(name,'u')),(1,('slack_'+name,'u')),(-(self.p-1),('u','u'))))
        yield Row('strict_modular_product',{},
                  ((1,('x','y')),(-1,('E','u')),(-self.p,('h','u'))))

    def boolean_rows(self):
        for i in range(1,self.witness_size):
            yield Row('homogeneous_boolean',{'coordinate':i},((1,(i,i)),(-1,(i,0))))

    def encode_forms(self,values):
        if set(values)!=set(self.forms):raise ValueError('exact form layout required')
        bits=[0]*self.witness_size
        for name,(offset,width) in self.forms.items():
            value=values[name]
            if type(value) is not int or not 0<=value<2**width:
                raise ValueError('noncanonical form: '+name)
            bits[offset:offset+width]=[(value>>j)&1 for j in range(width)]
        return tuple(bits)

    def encode(self,x,y,session=0,source_label=0,sequence=1):
        if any(type(v) is not int or not 0<=v<self.p for v in (x,y)):
            raise ValueError('noncanonical field input')
        h,E=divmod(x*y,self.p)
        values={'u':1,'x':x,'y':y,'E':E,'h':h,
                'slack_x':self.p-1-x,'slack_y':self.p-1-y,'slack_E':self.p-1-E}
        metadata=dict(session=session,source_label=source_label,sequence=sequence)
        for field,words in self.METADATA:
            value=metadata[field]
            if type(value) is not int or not 0<=value<2**(64*words):
                raise ValueError('noncanonical metadata: '+field)
            for j in range(words):values[f'{field}[{j}]']=(value>>(64*j))%(2**64)
        return self.encode_forms(values)

    def decode(self,bits):
        if len(bits)!=self.witness_size or any(type(b) is not int or b not in (0,1) for b in bits):
            raise ValueError('canonical scalar bits required')
        return {name:sum(bits[offset+j]<<j for j in range(width))
                for name,(offset,width) in self.forms.items()}

    def project(self,bits):
        values=self.decode(bits)
        return {name:values[name] for name in self.projection_names}

    def validate_public(self,public):
        if set(public)!=set(self.projection_names):raise ValueError('wrong public fields')
        for name,value in public.items():
            bound=2 if name=='u' else self.p if name=='E' else 2**64
            if type(value) is not int or not 0<=value<bound:
                raise ValueError('noncanonical public value')
        if public['u']!=1:raise ValueError('fresh u must be one')

    def embed_public(self,public):
        """Convert scalar wire encodings to the protocol's nine R_q outputs."""
        self.validate_public(public)
        return {name:(value,)+(0,)*(self.N-1) for name,value in public.items()}

    def check_batch_labels(self,publics,session_words,previous_sequence):
        return verify_batch_labels([self.embed_public(p) for p in publics],
                                   session_words,previous_sequence)

    def check(self,bits,public):
        self.validate_public(public);values=self.decode(bits)
        if self.project(bits)!=public:raise ValueError('not the same opening')
        if any(row.evaluate(values)!=0 for row in self.arithmetic_rows()):
            raise ValueError('invalid strict multiplication or range')
        return True

    def project_ring(self,witness):
        values=RingForms(self,witness)
        return {name:values[name] for name in self.projection_names}

    def evaluate_homogeneous_rows(self,witness,pad=True):
        values=RingForms(self,witness)
        for row in self.arithmetic_rows():yield row.evaluate_ring(values,self.N,self.q)
        u=values.coordinate(0)
        for i in range(1,self.witness_size):
            b=values.coordinate(i)
            square=negacyclic(b,b,self.q);linear=negacyclic(u,b,self.q)
            yield tuple((a-c)%self.q for a,c in zip(square,linear))
        if pad:
            for _ in range(1024-(self.witness_size-1+4)):yield (0,)*self.N

    def manifest(self):
        return {'semantic_relation':'one multiplication x*y=E in F_p',
                'not_implemented_here':'archived 512-coefficient R_p multiplication',
                'p':self.p,'q':self.q,'N':self.N,
                'core_coordinates_without_metadata':358,'metadata_bits':448,
                'witness_ring_coordinates':self.witness_size,
                'boolean_rows':self.witness_size-1,'arithmetic_rows':4,
                'polynomial_rows':self.witness_size+3,'padded_rows':1024,
                'homogeneous_degree':2,'public_projection_count':len(self.projection_names),
                'integer_residual_abs_bound':self.integer_residual_bound,
                'core_bits':7*51,'source_labels':'bound opaque labels; no owner authentication',
                'status':'SMALL_SEMANTIC_EXAMPLE_NOT_END_TO_END_IMPLEMENTATION'}
