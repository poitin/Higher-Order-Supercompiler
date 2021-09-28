# Higher-Order-Supercompiler
An implementation of the higher-order supercompilation algorithm as described in the paper ["On the Termination of Higher-Order Positive Supercompilation"](https://www.google.ie/url?sa=t&rct=j&q=&esrc=s&source=web&cd=&ved=2ahUKEwiug9Lk9qHzAhVEUMAKHU2lAvwQFnoECAMQAQ&url=https%3A%2F%2Feasychair.org%2Fpublications%2Fdownload%2FFJ&usg=AOvVaw2gvt1ee4yW-6p8I3PqEJFQ)

The implementation can be built and executed using stack.

## Execution 

The execution is a REPL, with the prompt "POT> " and the following commands:

```
POT> :help

:load filename          To load the given filename  
:prog                   To print the current program  
:term                   To print the current term  
:eval                   To evaluate the current program  
:super <filename>       To supercompile the current program. If the file name is provided, the result will be stored in the specified file.  
:quit                   To quit  
:help                   To print this message  
```

The first thing to do is to load a program file:

```
POT> :load appapp
```

This will load the program appapp.pot (the.pot extension is assumed).

To see the contents of this program:

```
POT> :prog  
main = append (append xs ys) zs;  
append xs ys = case xs of  
                    Nil -> ys  
                  | Cons(x,xs) -> Cons(x,append xs ys)  
```

To see the top-level term:

```
POT> :term  
append (append xs ys) zs
```

To apply the supercompilation transformation to the current program:

```
POT> :super  
main = f xs ys zs;  
f xs ys zs = case xs of  
                  Nil -> case ys of  
                              Nil -> zs  
                            | Cons(x,xs) -> Cons(x,f' xs zs)  
                | Cons(x,xs) -> Cons(x,f xs ys zs);  
f' xs' zs = case xs' of  
                 Nil -> zs  
               | Cons(x,xs) -> Cons(x,f' xs zs)  
```

To evaluate the current program:

```
POT> :eval
```

This will prompt for values of the free variables:

```
xs = [1,2,3]  
ys = [4,5,6]  
zs = [7,8,9]  
[1,2,3,4,5,6,7,8,9]  
Reductions: 101  
Allocations: 8  
```

To quit from the program:

```
POT> :quit
```

