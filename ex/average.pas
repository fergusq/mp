program average;

procedure readnums(nums : array of integer);
begin
    var i : integer;
    i := 0;
    while i < nums.size do begin
        read(nums[i]);
        i := i + 1;
    end;
end;

begin
    writeln("Give 4 values");
    var nums : array[4] of integer;
    readnums(nums);
    var sum : integer;
    sum := 0;
    var i : integer;
    i := 0;
    while i < 4 do begin
        sum := sum + nums[i];
        i := i + 1;
    end;
    writeln(sum/4);
end.
