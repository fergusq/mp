program example;
procedure f(a : integer);
begin
	g(a+1)
end;
procedure g(a : integer);
begin
	if a <= 5 then
		f(a)
	else
		writeln(a)
end;
begin
	f(0)
end.
