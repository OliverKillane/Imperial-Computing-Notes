# A B
A()
B()

# A | B (to be an LL(1) grammar, first sets must be disjoint)
if next_token() in first(A):
    A()
elif next_token() in first(B):
    B()

# {A}
while next_token() in first(A):
    A()

#[A]
if next_token() in first(A):
    A()
