program p;
begin var a:array[10]of integer;
var i:integer;
i:=0;
while i<a.size do begin a[i]:=i*2;
i:=i+1;
end;
var s:integer;
s:=0;
i:=0;
while i<a.size do begin s:=s+a[i];
i:=i+1 end;
writeln(s)end.
