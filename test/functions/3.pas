program p;
procedure f(var i:integer);
begin i:=i*2;
g(i)end;
procedure g(var i:integer);
begin i:=i+1 end;
begin var i:integer;
i:=5;
f(i);
writeln(i)end.
