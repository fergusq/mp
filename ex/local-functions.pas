program kissa;

var i : integer;
i := 10;

function f(i : integer) : integer;
begin
	return i+1
end;

procedure g(var x : integer);
begin
	function h() : integer;
	begin
		return i*2;
	end;
	x := x + h()
end;

begin
	var j : integer;
	read(j);
	j := f(j);
	g(j);
	writeln(j)
end.
