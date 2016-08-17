use strict;
our(@a,@aa,$find); #global variables
my $n=<DATA>;
while(<DATA>){  # input data
  push  @aa, [ split ];
}
for (my $k=0; $k < $n ; $k++){  # for each test puzzle
  $find=0;
  @a=@aa[$k*9..($k+1)*9-1]; # @a stores the current test puzzle
  &try_entry(0,0);  # try placing some number on the first entry (0,0)
  $find ? &print_sudoku_puzzle : print "NO\n";
}
sub try_entry{  # try placing some number on the entry (row,col)
  my($row,$col)=@_;
  if ($row >= 9) { # all entries are done => the puzzle is solved
	$find=1;	
	return;
  }  
  my $next_row=int(($row*9+$col+1)/9); # the next entry's row number
  my $next_col=($row*9+$col+1)%9; # the next entry's col number
  if ($a[$row][$col] > 0){  # the position (row,col) is not blank
     &try_entry($next_row,$next_col);	 # try the next entry
  }else{ # try placing some number from 1 to 9 on position (row,col)     
     for (my $s=1; !$find && $s <= 9 ; $s++){ 
	    my $conflict=0;
		$conflict=1 if grep( $_ == $s, @{$a[$row]} ); # check entries on the same row 
		$conflict=1 if grep( $_ == $s, (map $_->[$col], @a)); # check entries on the same column
		for (my $i=int($row/3)*3, my $ii=0; $ii < 3; $i++,$ii++){ 
		  for (my $j=int($col/3)*3, my $jj=0; $jj < 3; $j++,$jj++){
		    $conflict=1 if ($a[$i][$j]==$s); # check entries on the same block
		  }
		}  	
        if (!$conflict){ 
		  $a[$row][$col]=$s; # try placing number s on position (row,col)
		  &try_entry($next_row,$next_col); # try the next entry
		}		
	 } # end of for s loop
	 $a[$row][$col]=0 if !$find; # reset to  0 
  } # end of else
} # end of sub try_entry
sub print_sudoku_puzzle{
  for my $sub_array (@a){
    print join(" ",@{$sub_array}),"\n";
  }	
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
