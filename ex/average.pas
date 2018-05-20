program average;

{* lukee lukuja annettuun taulukkoon *}
procedure readnums(nums : array of real);
begin
    var i : integer;
    i := 0;
    while i < nums.size do begin
        read(nums[i]);
        while (nums[i] < 1.0e-2) or (nums[i] > 1.0e2) do begin
            writeln(nums[i], "is either too large or too small. Try again (enter number 0.01>=n>=100):");
            read(nums[i]);
        end;
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
