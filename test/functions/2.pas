program p;
function f(var i:integer):integer;
begin i:=i*2;
return i end;
begin var x:integer;
x:=2;
writeln(f(x),f(x),f(x))end.
