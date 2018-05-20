program p;
begin var i:integer;
i:=7;
while i<>1 do begin writeln(i);
 if i%2=0 then i:=i/2 else i:=i*3+1;
end;
end.
