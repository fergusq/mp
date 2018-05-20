program example2;
procedure sum(a : array[10] of integer, var n : integer);
begin
	var i : integer;
	i := 0;
	n := 0;
	while i < 10 do begin
		n := n + a[i];
		i := i + 1;
	end
end;
begin
	var n : integer;
	var a : array[10] of integer;
	n := 9;
	while n >= 0 do begin
		read(a[n]);
		n := n - 1
	end;
	sum(a, n);
	writeln(n)
end.
