use strict;
our @a; # a global 2D array which stores all test puzzles
my $n=<DATA>; # read the number of test puzzles
push @a,[split] while(<DATA>); # read all test puzzles 
for (1..$n){  # for each test puzzle  
  &try_entry(0,0) ? map print(join " ",@{$_},"\n"),@a[0..8] : print "NO\n"; # if the puzzle is solved, print the solution
  splice @a,0,9;  #remove the puzzle from @a which has been tested
}
sub try_entry{  # try placing some number on the entry (row,col)
  my($row,$col)=@_;
  return 1 if ($row == 9);  # all 9*9 entries are done and return success
  my ($bk_row,$bk_col,$next_row,$next_col)=(int($row/3)*3,int($col/3)*3,int(($row*9+$col+1)/9),($row*9+$col+1)%9);
  return &try_entry($next_row,$next_col) if ($a[$row][$col] > 0);  # the entry (row,col) is not blank and try the next entry     	 
  for my $s (1..9){# try placing number s from 1 to 9 on entry (row,col)               
    unless(grep($_==$s,@{$a[$row]})||grep($_==$s,(map $_->[$col],@a[0..8]))||grep($_==$s,(@{$a[$bk_row]}[$bk_col..$bk_col+2],@{$a[$bk_row+1]}[$bk_col..$bk_col+2],@{$a[$bk_row+2]}[$bk_col..$bk_col+2]))){ # the 3 rules of Sudoku
      $a[$row][$col]=$s; # place number s on entry (row,col)
      return 1 if &try_entry($next_row,$next_col); # try the next entry and if it successes then return success
	} 		
  } 
  return $a[$row][$col]=0;  # entry (row,col) is reset to blank and return failure
} 
__DATA__
2
0 0 0 4 0 0 9 3 0
0 0 5 0 0 0 6 0 0
0 0 0 2 0 0 0 0 0
0 0 0 0 0 0 0 9 0
0 8 3 0 4 0 0 0 5
0 9 1 7 0 0 0 0 6
0 0 7 5 0 0 0 0 0
0 0 0 1 0 9 0 0 7
0 0 0 3 0 2 0 0 0
3 0 0 0 0 0 0 0 0
7 0 0 0 0 0 0 0 5
0 0 8 2 6 0 0 3 0
9 1 0 0 0 0 0 6 3
0 4 0 9 0 0 0 0 0
0 0 2 0 7 0 0 0 0
0 2 4 0 0 0 0 0 0
0 5 0 4 0 6 3 0 0
0 0 0 0 0 8 0 0 0

__OUTPUT__
1 2 6 4 5 7 9 3 8
4 7 5 8 9 3 6 1 2
8 3 9 2 1 6 5 7 4
7 5 4 6 2 8 1 9 3
6 8 3 9 4 1 7 2 5
2 9 1 7 3 5 8 4 6
3 1 7 5 6 4 2 8 9
5 4 2 1 8 9 3 6 7
9 6 8 3 7 2 4 5 1
NO
