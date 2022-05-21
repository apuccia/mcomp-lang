## Linking

Given a connection 
```
ID1.ID2 <- ID3.ID4
```
The linker must ensure that:
- [x] `ID1` and `ID3` are the names of two different components.
- [x] `ID2` is the name of an interface *used* by `ID1`.
- [x] `ID4` is the name of an interface *provided* by `ID3`.
- [x] `ID2` and `ID4` are the same interface.

[x] After establishing a connection between 2 components it can't be overwritten.
[x] The linker has to ensure that for each component every used interfaces are linked.
[x] The linker has to qualify function calls and variables with the components that implements them.

## Code extensions

Students are required to implement **at least two** of the following constructs: 
- [x] `do-while` loops;
- [x] pre/post increment/decrement operators, i.e., `++` and `--`;
- [x] abbreviation for assignment operators, i.e., `+=`, `-=`, `*=`, `/=` and `%=`;
- [ ] variable declaration with initialization, e.g., `var i : int = 0`;
- [ ] multi-dimensional arrays;
- [x] floating point arithmetic;
- [ ] strings of characters;
- [ ] inheritance among interfaces;
- [ ] interfaces that can use other interfaces;
- [ ] overloading of functions. 