program average;

{* lukee lukuja annettuun taulukkoon *}
procedure readnums(nums : array of real);
begin
    var i : integer;
    i := 0;
    while i < nums.size do begin
        read(nums[i]);
        i := i + 1;
    end;
end;

begin
    var n : integer;
    
    writeln("Give N:");
    read(n);
    
    writeln("Give", n, "values:");
    
    var nums : array of real;
    nums := make_real_array(n);
    readnums(nums);
    
    var sum : real;
    sum := 0.0;
    var i : integer;
    i := 0;
    while i < n do begin
        sum := sum + nums[i];
        i := i + 1;
    end;
    writeln(sum/integer_to_real(n));
end.
