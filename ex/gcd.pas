program gcd;
begin
	var a, b, t : integer;
	read(a, b);
	while b <> 0 do begin
		t := b;
		b := a % b;
		a := t
	end;
	writeln(a);
end.
