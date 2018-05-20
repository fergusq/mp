program references;

procedure f(var a : integer, var b : integer, var c : integer);
begin
	a := 1;
	b := 2;
	c := 3
end;

procedure main(var x : integer);
begin
	var a : array[1] of integer;
	var i : integer;
	f(i, x, a[0]);
	writeln(i, x, a[0])
end;

begin
	var x : integer;
	main(x)
end.
