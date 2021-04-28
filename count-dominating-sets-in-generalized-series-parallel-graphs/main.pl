#!/usr/bin/perl
#
# Count independent sets, dominating sets, independent dominating sets (maximal independent sets), connected dominating sets,
# total dominating sets and independent perfect dominating sets in a generalized series-parallel graph
#
# Time complexity: O(n)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph::Undirected;

#globals
$m=14; 	# number of edges; problem size 
@OP=@L=@R=();
$g=();
 
while ( $test++ < 10000 ){ # test 10000 random instances	
	&new_g(); # create a random generalized series-parallel graph
		
	print "\n== test $test: generalized series-parallel graph: ==\n";	
	print "g: $g\n";
	#for($i=0; $i < @OP ; $i++){	
	#	print "($i:$OP[$i],$L[$i],$R[$i]) ";
	#}
	#print "\n";
	print "our proposed algorithm	 : ";		
	$IS1=&IS();	
	$IDS1=&IDS();
	$IPDS1=&IPDS(); 
	$DS1=&DS();
	$CDS1=&CDS();
	$TDS1=&TDS();
	print "IS=$IS1, DS=$DS1, IDS=$IDS1, IPDS=$IPDS1, TDS=$TDS1, CDS=$CDS1\n";
	
	print "the brute-force algorithm: ";
	($IS2,$IDS2,$IPDS2,$DS2,$CDS2,$TDS2)=&brute_force();
	print "IS=$IS2, DS=$DS2, IDS=$IDS2, IPDS=$IPDS2, TDS=$TDS2, CDS=$CDS2\n";

	if( $IS1!=$IS2 || $DS1 != $DS2 || $IDS1 != $IDS2 || $IPDS1 != $IPDS2 || $TDS1 != $TDS2 || $CDS1 != $CDS2 ){
		print "An error occured. Stop!\n";
		exit;
	}	
}										 
print "\n Tests completed successfully.\n";

# count independent sets (ISs) in a generalized series-parallel graph
sub IS {
	my(@AA,@AB,@BA,@BB,$i,$i1,$i2);	
	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$AA[$k]=0;
			$AB[$k]=$BA[$k]=$BB[$k]=1;
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$AA[$k]=$AA[$i]*$AA[$j];
				$AB[$k]=$AB[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j];
				$BB[$k]=$BB[$i]*$BB[$j];
			}elsif($OP[$k] eq 's'){ # series operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AB[$i]*$BA[$j];
				$AB[$k]=$AA[$i]*$AB[$j]+$AB[$i]*$BB[$j];
				$BA[$k]=$BB[$i]*$BA[$j]+$BA[$i]*$AA[$j];
				$BB[$k]=$BA[$i]*$AB[$j]+$BB[$i]*$BB[$j];
			}else{ # dangling operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AA[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$BB[$j];
				$AB[$k]=$AB[$i]*$AA[$j]+$AB[$i]*$AB[$j];
				$BB[$k]=$BB[$i]*$BA[$j]+$BB[$i]*$BB[$j];				
			}
		}			
	} # for
	
	return($AA[$k-1]+$AB[$k-1]+$BA[$k-1]+$BB[$k-1]);
} # end of IS


# count dominating sets (DSs) in a generalized series-parallel graph
# note: the same as IDS except the initial condition of (AA=1)
sub DS {
	my(@AA,@AB,@BA,@BB,@AC,@CA,@BC,@CB,@CC,$k,$i,$j);	
	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$AA[$k]=1; $BB[$k]=0;
			$AB[$k]=$BA[$k]=1;
			$AC[$k]=$CA[$k]=0;
			$BC[$k]=$CB[$k]=0;
			$CC[$k]=1; # or 0 ? check!
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$AA[$k]=$AA[$i]*$AA[$j];
				$AB[$k]=$AB[$i]*$AB[$j]+$AB[$i]*$AC[$j]+$AC[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$CA[$j]+$CA[$i]*$BA[$j];
				$BB[$k]=$BB[$i]*$BB[$j]+$BB[$i]*$BC[$j]+$BC[$i]*$BB[$j]+$CB[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$CC[$j]+$CC[$i]*$BB[$j]+$BC[$i]*$CB[$j]+$CB[$i]*$BC[$j];
				$AC[$k]=$AC[$i]*$AC[$j];
				$CA[$k]=$CA[$i]*$CA[$j];
				$BC[$k]=$BC[$i]*$BC[$j]+$BC[$i]*$CC[$j]+$CC[$i]*$BC[$j];
				$CB[$k]=$CB[$i]*$CB[$j]+$CB[$i]*$CC[$j]+$CC[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CC[$j];
			}elsif($OP[$k] eq 's'){ # series operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AC[$i]*$BA[$j]+$AB[$i]*$CA[$j]+$AB[$i]*$BA[$j];
				$AB[$k]=$AA[$i]*$AB[$j]+$AC[$i]*$BB[$j]+$AB[$i]*$CB[$j]+$AB[$i]*$BB[$j];
				$BA[$k]=$BA[$i]*$AA[$j]+$BC[$i]*$BA[$j]+$BB[$i]*$CA[$j]+$BB[$i]*$BA[$j];
				$BB[$k]=$BA[$i]*$AB[$j]+$BC[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$BB[$j];
				$AC[$k]=$AA[$i]*$AC[$j]+$AC[$i]*$BC[$j]+$AB[$i]*$CC[$j]+$AB[$i]*$BC[$j];
				$CA[$k]=$CA[$i]*$AA[$j]+$CC[$i]*$BA[$j]+$CB[$i]*$CA[$j]+$CB[$i]*$BA[$j];
				$BC[$k]=$BA[$i]*$AC[$j]+$BC[$i]*$BC[$j]+$BB[$i]*$CC[$j]+$BB[$i]*$BC[$j];
				$CB[$k]=$CA[$i]*$AB[$j]+$CC[$i]*$BB[$j]+$CB[$i]*$CB[$j]+$CB[$i]*$BB[$j];
				$CC[$k]=$CA[$i]*$AC[$j]+$CC[$i]*$BC[$j]+$CB[$i]*$CC[$j]+$CB[$i]*$BC[$j];
			}else{ # dangling operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AA[$i]*$AB[$j];
				$AB[$k]=$AB[$i]*$AA[$j]+$AB[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$BB[$j]+$BA[$i]*$CA[$j]+$BA[$i]*$CB[$j]+$CA[$i]*$BA[$j]+$CA[$i]*$BB[$j];				
				$BB[$k]=$BB[$i]*$BA[$j]+$BB[$i]*$BB[$j]+$BB[$i]*$CA[$j]+$BB[$i]*$CB[$j]+$CB[$i]*$BA[$j]+$CB[$i]*$BB[$j];
				$AC[$k]=$AC[$i]*$AA[$j]+$AC[$i]*$AB[$j];				
				$CA[$k]=$CA[$i]*$CA[$j]+$CA[$i]*$CB[$j];
				$BC[$k]=$BC[$i]*$BA[$j]+$BC[$i]*$BB[$j]+$BC[$i]*$CA[$j]+$BC[$i]*$CB[$j]+$CC[$i]*$BA[$j]+$CC[$i]*$BB[$j];				
				$CB[$k]=$CB[$i]*$CA[$j]+$CB[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CA[$j]+$CC[$i]*$CB[$j];		
			}
		}	
	} # for	
	return($AA[$k-1]+$AB[$k-1]+$BA[$k-1]+$BB[$k-1]);
} # end of DS

# count independent dominating sets (IDSs) in a generalized series-parallel graph
# note: the same as DS except the initial condition of (AA=0)
sub IDS {
	my(@AA,@AB,@BA,@BB,@AC,@CA,@BC,@CB,@CC,$k,$i,$j);	
	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$AA[$k]=$BB[$k]=0;
			$AB[$k]=$BA[$k]=1;
			$AC[$k]=$CA[$k]=0;
			$BC[$k]=$CB[$k]=0;
			$CC[$k]=1; # or 0 ? check!
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$AA[$k]=$AA[$i]*$AA[$j];
				$AB[$k]=$AB[$i]*$AB[$j]+$AB[$i]*$AC[$j]+$AC[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$CA[$j]+$CA[$i]*$BA[$j];
				$BB[$k]=$BB[$i]*$BB[$j]+$BB[$i]*$BC[$j]+$BC[$i]*$BB[$j]+$CB[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$CC[$j]+$CC[$i]*$BB[$j]+$BC[$i]*$CB[$j]+$CB[$i]*$BC[$j];
				$AC[$k]=$AC[$i]*$AC[$j];
				$CA[$k]=$CA[$i]*$CA[$j];
				$BC[$k]=$BC[$i]*$BC[$j]+$BC[$i]*$CC[$j]+$CC[$i]*$BC[$j];
				$CB[$k]=$CB[$i]*$CB[$j]+$CB[$i]*$CC[$j]+$CC[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CC[$j];
			}elsif($OP[$k] eq 's'){ # series operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AC[$i]*$BA[$j]+$AB[$i]*$CA[$j]+$AB[$i]*$BA[$j];
				$AB[$k]=$AA[$i]*$AB[$j]+$AC[$i]*$BB[$j]+$AB[$i]*$CB[$j]+$AB[$i]*$BB[$j];
				$BA[$k]=$BA[$i]*$AA[$j]+$BC[$i]*$BA[$j]+$BB[$i]*$CA[$j]+$BB[$i]*$BA[$j];
				$BB[$k]=$BA[$i]*$AB[$j]+$BC[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$BB[$j];
				$AC[$k]=$AA[$i]*$AC[$j]+$AC[$i]*$BC[$j]+$AB[$i]*$CC[$j]+$AB[$i]*$BC[$j];
				$CA[$k]=$CA[$i]*$AA[$j]+$CC[$i]*$BA[$j]+$CB[$i]*$CA[$j]+$CB[$i]*$BA[$j];
				$BC[$k]=$BA[$i]*$AC[$j]+$BC[$i]*$BC[$j]+$BB[$i]*$CC[$j]+$BB[$i]*$BC[$j];
				$CB[$k]=$CA[$i]*$AB[$j]+$CC[$i]*$BB[$j]+$CB[$i]*$CB[$j]+$CB[$i]*$BB[$j];
				$CC[$k]=$CA[$i]*$AC[$j]+$CC[$i]*$BC[$j]+$CB[$i]*$CC[$j]+$CB[$i]*$BC[$j];
			}else{ # dangling operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AA[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$BB[$j]+$BA[$i]*$CA[$j]+$BA[$i]*$CB[$j]+$CA[$i]*$BA[$j]+$CA[$i]*$BB[$j];
				$AB[$k]=$AB[$i]*$AA[$j]+$AB[$i]*$AB[$j];
				$BB[$k]=$BB[$i]*$BA[$j]+$BB[$i]*$BB[$j]+$BB[$i]*$CA[$j]+$BB[$i]*$CB[$j]+$CB[$i]*$BA[$j]+$CB[$i]*$BB[$j];
				$CA[$k]=$CA[$i]*$CA[$j]+$CA[$i]*$CB[$j];
				$AC[$k]=$AC[$i]*$AA[$j]+$AC[$i]*$AB[$j];
				$CB[$k]=$CB[$i]*$CA[$j]+$CB[$i]*$CB[$j];
				$BC[$k]=$BC[$i]*$BA[$j]+$BC[$i]*$BB[$j]+$BC[$i]*$CA[$j]+$BC[$i]*$CB[$j]+$CC[$i]*$BA[$j]+$CC[$i]*$BB[$j];
				$CC[$k]=$CC[$i]*$CA[$j]+$CC[$i]*$CB[$j];		
			}
		}	
	} # for		
	return($AA[$k-1]+$AB[$k-1]+$BA[$k-1]+$BB[$k-1]);
} # end of IDS

# count independent perfect dominating sets (IPDSs) in a generalized series-parallel graph
sub IPDS { # for multi-graph
	my(@AA,@AB,@AB0,@AB1,@B0A,@B1A,@BA,@BB,@AC,@CA,@BC,@CB,@CC,$k,$i,$j);
	# AB0,B0A: A does not dominate B; (s,t) not in E		
	# AB1,B1A: A dominates B; (s,t) in E

	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$AA[$k]=$BB[$k]=0;
			$AB1[$k]=$B1A[$k]=1;
			$AB0[$k]=$B0A[$k]=0;
			$AB[$k]=$AB0[$k]+$AB1[$k];
			$BA[$k]=$B0A[$k]+$B1A[$k];
			$AC[$k]=$CA[$k]=0;
			$BC[$k]=$CB[$k]=0;
			$CC[$k]=1; # or 0 ? check!
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$AA[$k]=$AA[$i]*$AA[$j];
				
				$AB0[$k]=$AB0[$i]*$AC[$j]+$AC[$i]*$AB0[$j]; 
				$AB1[$k]=$AB1[$i]*$AC[$j]+$AC[$i]*$AB1[$j]+$AB1[$i]*$AB1[$j]; 
				$AB[$k]=$AB0[$k]+$AB1[$k];
				
				$B0A[$k]=$B0A[$i]*$CA[$j]+$CA[$i]*$B0A[$j];				
				$B1A[$k]=$B1A[$i]*$CA[$j]+$CA[$i]*$B1A[$j]+$B1A[$i]*$B1A[$j];				
				$BA[$k]=$B0A[$k]+$B1A[$k];
				
				$BB[$k]=$BB[$i]*$CC[$j]+$CC[$i]*$BB[$j]+$BC[$i]*$CB[$j]+$CB[$i]*$BC[$j];
				$AC[$k]=$AC[$i]*$AC[$j];
				$CA[$k]=$CA[$i]*$CA[$j];
				$BC[$k]=$BC[$i]*$CC[$j]+$CC[$i]*$BC[$j];
				$CB[$k]=$CB[$i]*$CC[$j]+$CC[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CC[$j];
			}elsif($OP[$k] eq 's'){ # series operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AC[$i]*$BA[$j]+$AB[$i]*$CA[$j];
				
				$AB0[$k]=$AA[$i]*$AB[$j]+$AC[$i]*$BB[$j]+$AB[$i]*$CB[$j];
				$AB1[$k]=0;
				$AB[$k]=$AB0[$k]+$AB1[$k];
				
				$B0A[$k]=$BA[$i]*$AA[$j]+$BC[$i]*$BA[$j]+$BB[$i]*$CA[$j];
				$B1A[$k]=0;
				$BA[$k]=$B0A[$k]+$B1A[$k];
				
				$BB[$k]=$BA[$i]*$AB[$j]+$BC[$i]*$BB[$j]+$BB[$i]*$CB[$j];
				$AC[$k]=$AA[$i]*$AC[$j]+$AC[$i]*$BC[$j]+$AB[$i]*$CC[$j];
				$CA[$k]=$CA[$i]*$AA[$j]+$CC[$i]*$BA[$j]+$CB[$i]*$CA[$j];
				$BC[$k]=$BA[$i]*$AC[$j]+$BC[$i]*$BC[$j]+$BB[$i]*$CC[$j];
				$CB[$k]=$CA[$i]*$AB[$j]+$CC[$i]*$BB[$j]+$CB[$i]*$CB[$j];
				$CC[$k]=$CA[$i]*$AC[$j]+$CC[$i]*$BC[$j]+$CB[$i]*$CC[$j];
			}else{ # dangling operation
				$AA[$k]=$AA[$i]*$AA[$j]+$AA[$i]*$AB[$j];
				
				$B0A[$k]=$B0A[$i]*$CA[$j]+$B0A[$i]*$CB[$j]+$CA[$i]*$BA[$j]+$CA[$i]*$BB[$j];
				$B1A[$k]=$B1A[$i]*$CA[$j]+$B1A[$i]*$CB[$j];
				$BA[$k]=$B0A[$k]+$B1A[$k];
				
				$AB0[$k]=$AB0[$i]*$AA[$j]+$AB0[$i]*$AB[$j];
				$AB1[$k]=$AB1[$i]*$AA[$j]+$AB1[$i]*$AB[$j];;
				$AB[$k]=$AB0[$k]+$AB1[$k];
				
				$BB[$k]=$BB[$i]*$CA[$j]+$BB[$i]*$CB[$j]+$CB[$i]*$BA[$j]+$CB[$i]*$BB[$j];
				$CA[$k]=$CA[$i]*$CA[$j]+$CA[$i]*$CB[$j];
				$AC[$k]=$AC[$i]*$AA[$j]+$AC[$i]*$AB[$j];
				$CB[$k]=$CB[$i]*$CA[$j]+$CB[$i]*$CB[$j];
				$BC[$k]=$BC[$i]*$CA[$j]+$BC[$i]*$CB[$j]+$CC[$i]*$BA[$j]+$CC[$i]*$BB[$j];
				$CC[$k]=$CC[$i]*$CA[$j]+$CC[$i]*$CB[$j];					
			}
		}	
	} # for	
	return($AA[$k-1]+$AB[$k-1]+$BA[$k-1]+$BB[$k-1]);
} # end of IPDS


# count total dominating sets (TDSs) in a generalized series-parallel graph
sub TDS {
	my(@A0A0,@A0A1,@A1A0,@A1A1,@A0B,@A1B,@BA0,@BA1,@BB,@A0C,@A1C,@CA0,@CA1,@BC,@CB,@CC,$k,$i,$j);
	# For i,j in {0,1}, AiAj, AiB, BAj, AiC, CAj are defined as
	# i=0(j=0) denotes s(t) is a dominating vertex but s(t) is not dominated by others dominating vertices
	# i=1(j=1) denotes s(t) is a dominating vertex and s(t) is dominated by others dominating vertices
	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$A0A0[$k]=0; $A0A1[$k]=0; $A1A0[$k]=0; $A1A1[$k]=1;			
			$BB[$k]=0;
			$A0B[$k]=$BA0[$k]=1;$A1B[$k]=$BA1[$k]=0;
			$A0C[$k]=$CA0[$k]=0;$A1C[$k]=$CA1[$k]=0; # check!
			$BC[$k]=$CB[$k]=0;
			$CC[$k]=1; # or 0 ? check!
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$A0A0[$k]=$A0A0[$i]*$A0A0[$j];
				$A0A1[$k]=$A0A0[$i]*$A0A1[$j]+$A0A1[$i]*$A0A0[$j]+$A0A1[$i]*$A0A1[$j];
				$A1A0[$k]=$A0A0[$i]*$A1A0[$j]+$A1A0[$i]*$A0A0[$j]+$A1A0[$i]*$A1A0[$j];
				$A1A1[$k]=$A0A0[$i]*$A1A1[$j]+$A1A0[$i]*$A0A1[$j]+$A1A0[$i]*$A1A1[$j]+
									$A0A1[$i]*$A1A0[$j]+$A1A1[$i]*$A0A0[$j]+$A1A1[$i]*$A1A0[$j]+
									$A0A1[$i]*$A1A1[$j]+$A1A1[$i]*$A0A1[$j]+$A1A1[$i]*$A1A1[$j];
				$A0B[$k]=$A0B[$i]*$A0B[$j]+$A0B[$i]*$A0C[$j]+$A0C[$i]*$A0B[$j];
				$A1B[$k]=$A0B[$i]*$A1B[$j]+$A1B[$i]*$A0B[$j]+$A1B[$i]*$A1B[$j]+
								 $A0B[$i]*$A1C[$j]+$A1B[$i]*$A0C[$j]+$A1B[$i]*$A1C[$j]+
								 $A0C[$i]*$A1B[$j]+$A1C[$i]*$A0B[$j]+$A1C[$i]*$A1B[$j];
				$BA0[$k]=$BA0[$i]*$BA0[$j]+$BA0[$i]*$CA0[$j]+$CA0[$i]*$BA0[$j];
				$BA1[$k]=$BA0[$i]*$BA1[$j]+$BA1[$i]*$BA0[$j]+$BA1[$i]*$BA1[$j]+
								 $BA0[$i]*$CA1[$j]+$BA1[$i]*$CA0[$j]+$BA1[$i]*$CA1[$j]+
								 $CA0[$i]*$BA1[$j]+$CA1[$i]*$BA0[$j]+$CA1[$i]*$BA1[$j];
				$BB[$k]=$BB[$i]*$BB[$j]+$BB[$i]*$BC[$j]+$BC[$i]*$BB[$j]+$CB[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$CC[$j]+
								$CC[$i]*$BB[$j]+$BC[$i]*$CB[$j]+$CB[$i]*$BC[$j];
				$A0C[$k]=$A0C[$i]*$A0C[$j];
				$A1C[$k]=$A0C[$i]*$A1C[$j]+$A1C[$i]*$A0C[$j]+$A1C[$i]*$A1C[$j];
				$CA0[$k]=$CA0[$i]*$CA0[$j];
				$CA1[$k]=$CA0[$i]*$CA1[$j]+$CA1[$i]*$CA0[$j]+$CA1[$i]*$CA1[$j];				
				$BC[$k]=$BC[$i]*$BC[$j]+$BC[$i]*$CC[$j]+$CC[$i]*$BC[$j];
				$CB[$k]=$CB[$i]*$CB[$j]+$CB[$i]*$CC[$j]+$CC[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CC[$j];
			}elsif($OP[$k] eq 's'){ # series operation				
				$A0A0[$k]=$A0A0[$i]*$A1A0[$j]+$A0A1[$i]*$A0A0[$j]+$A0A1[$i]*$A1A0[$j]+
									$A0C[$i]*$BA0[$j]+$A0B[$i]*$CA0[$j]+$A0B[$i]*$BA0[$j];				
				$A0A1[$k]=$A0A0[$i]*$A1A1[$j]+$A0A1[$i]*$A0A1[$j]+$A0A1[$i]*$A1A1[$j]+
									$A0C[$i]*$BA1[$j]+$A0B[$i]*$CA1[$j]+$A0B[$i]*$BA1[$j];				
				$A1A0[$k]=$A1A0[$i]*$A1A0[$j]+$A1A1[$i]*$A0A0[$j]+$A1A1[$i]*$A1A0[$j]+
									$A1C[$i]*$BA0[$j]+$A1B[$i]*$CA0[$j]+$A1B[$i]*$BA0[$j];				
				$A1A1[$k]=$A1A0[$i]*$A1A1[$j]+$A1A1[$i]*$A0A1[$j]+$A1A1[$i]*$A1A1[$j]+
									$A1C[$i]*$BA1[$j]+$A1B[$i]*$CA1[$j]+$A1B[$i]*$BA1[$j];				
				$A0B[$k]=$A0A0[$i]*$A1B[$j]+$A0A1[$i]*$A0B[$j]+$A0A1[$i]*$A1B[$j]+
								 $A0C[$i]*$BB[$j]+$A0B[$i]*$CB[$j]+$A0B[$i]*$BB[$j];
				$A1B[$k]=$A1A0[$i]*$A1B[$j]+$A1A1[$i]*$A0B[$j]+$A1A1[$i]*$A1B[$j]+
								 $A1C[$i]*$BB[$j]+$A1B[$i]*$CB[$j]+$A1B[$i]*$BB[$j];
				$BA0[$k]=$BA0[$i]*$A1A0[$j]+$BA1[$i]*$A0A0[$j]+$BA1[$i]*$A1A0[$j]+
								 $BC[$i]*$BA0[$j]+$BB[$i]*$CA0[$j]+$BB[$i]*$BA0[$j];				
				$BA1[$k]=$BA0[$i]*$A1A1[$j]+$BA1[$i]*$A0A1[$j]+$BA1[$i]*$A1A1[$j]+
								 $BC[$i]*$BA1[$j]+$BB[$i]*$CA1[$j]+$BB[$i]*$BA1[$j];
				$BB[$k]=$BA0[$i]*$A1B[$j]+$BA1[$i]*$A0B[$j]+$BA1[$i]*$A1B[$j]+
								$BC[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$BB[$i]*$BB[$j];
				$A0C[$k]=$A0A0[$i]*$A1C[$j]+$A0A1[$i]*$A0C[$j]+$A0A1[$i]*$A1C[$j]+
								 $A0C[$i]*$BC[$j]+$A0B[$i]*$CC[$j]+$A0B[$i]*$BC[$j];
				$A1C[$k]=$A1A0[$i]*$A1C[$j]+$A1A1[$i]*$A0C[$j]+$A1A1[$i]*$A1C[$j]+
								 $A1C[$i]*$BC[$j]+$A1B[$i]*$CC[$j]+$A1B[$i]*$BC[$j];
				$CA0[$k]=$CA0[$i]*$A1A0[$j]+$CA1[$i]*$A0A0[$j]+$CA1[$i]*$A1A0[$j]+
								 $CC[$i]*$BA0[$j]+$CB[$i]*$CA0[$j]+$CB[$i]*$BA0[$j];
				$CA1[$k]=$CA0[$i]*$A1A1[$j]+$CA1[$i]*$A0A1[$j]+$CA1[$i]*$A1A1[$j]+
								 $CC[$i]*$BA1[$j]+$CB[$i]*$CA1[$j]+$CB[$i]*$BA1[$j];
				$BC[$k]=$BA0[$i]*$A1C[$j]+$BA1[$i]*$A0C[$j]+$BA1[$i]*$A1C[$j]+
								$BC[$i]*$BC[$j]+$BB[$i]*$CC[$j]+$BB[$i]*$BC[$j];
				$CB[$k]=$CA0[$i]*$A1B[$j]+$CA1[$i]*$A0B[$j]+$CA1[$i]*$A1B[$j]+
								$CC[$i]*$BB[$j]+$CB[$i]*$CB[$j]+$CB[$i]*$BB[$j];
				$CC[$k]=$CA0[$i]*$A1C[$j]+$CA1[$i]*$A0C[$j]+$CA1[$i]*$A1C[$j]+
								$CC[$i]*$BC[$j]+$CB[$i]*$CC[$j]+$CB[$i]*$BC[$j];
			}else{ # dangling operation
				$A0A0[$k]=$A0A0[$i]*$A0A1[$j]+$A0A0[$i]*$A0B[$j];
				$A0A1[$k]=$A0A1[$i]*$A0A1[$j]+$A0A1[$i]*$A0B[$j];				
				$A1A0[$k]=$A0A0[$i]*$A1A1[$j]+$A1A0[$i]*$A0A1[$j]+$A1A0[$i]*$A1A1[$j]+
									$A0A0[$i]*$A1B[$j]+$A1A0[$i]*$A0B[$j]+$A1A0[$i]*$A1B[$j];
				$A1A1[$k]=$A0A1[$i]*$A1A1[$j]+$A1A1[$i]*$A0A1[$j]+$A1A1[$i]*$A1A1[$j]+
									$A0A1[$i]*$A1B[$j]+$A1A1[$i]*$A0B[$j]+$A1A1[$i]*$A1B[$j];				
				$A0B[$k]=$A0B[$i]*$A0A1[$j]+$A0B[$i]*$A0B[$j];									
				$A1B[$k]=$A0B[$i]*$A1A1[$j]+$A1B[$i]*$A0A1[$j]+$A1B[$i]*$A1A1[$j]+
								 $A0B[$i]*$A1B[$j]+$A1B[$i]*$A0B[$j]+$A1B[$i]*$A1B[$j];				
				$BA0[$k]=$BA0[$i]*$BA1[$j]+$BA0[$i]*$CA1[$j]+$CA0[$i]*$BA1[$j]+
								 $BA0[$i]*$BB[$j]+$BA0[$i]*$CB[$j]+$CA0[$i]*$BB[$j];
				$BA1[$k]=$BA1[$i]*$BA1[$j]+$BA1[$i]*$CA1[$j]+$CA1[$i]*$BA1[$j]+
								 $BA1[$i]*$BB[$j]+$BA1[$i]*$CB[$j]+$CA1[$i]*$BB[$j];				
				$BB[$k]=$BB[$i]*$BA1[$j]+$BB[$i]*$CA1[$j]+$CB[$i]*$BA1[$j]+
								$BB[$i]*$BB[$j]+$BB[$i]*$CB[$j]+$CB[$i]*$BB[$j];								
				$A0C[$k]=$A0C[$i]*$A0A1[$j]+$A0C[$i]*$A0B[$j];											
				$A1C[$k]=$A0C[$i]*$A1A1[$j]+$A1C[$i]*$A0A1[$j]+$A1C[$i]*$A1A1[$j]+
								 $A0C[$i]*$A1B[$j]+$A1C[$i]*$A0B[$j]+$A1C[$i]*$A1B[$j];				
				$CA0[$k]=$CA0[$i]*$CA1[$j]+$CA0[$i]*$CB[$j];
				$CA1[$k]=$CA1[$i]*$CA1[$j]+$CA1[$i]*$CB[$j];
				$BC[$k]=$BC[$i]*$BA1[$j]+$CC[$i]*$BA1[$j]+$BC[$i]*$CA1[$j]+
								$BC[$i]*$BB[$j]+$CC[$i]*$BB[$j]+$BC[$i]*$CB[$j];				
				$CB[$k]=$CB[$i]*$CA1[$j]+$CB[$i]*$CB[$j];
				$CC[$k]=$CC[$i]*$CA1[$j]+$CC[$i]*$CB[$j];								
			}
			
		}	
	} # for
	return($A1A1[$k-1]+$A1B[$k-1]+$BA1[$k-1]+$BB[$k-1]);
}


# count connected dominating sets (CDSs) in a generalized series-parallel graph
sub CDS {
	my(@AA1,@AA2,@AB,@BA,@BB,@AC,@CA,@BC,@CB,@CC,@BC0,@CB0,@CC0,$k,$i,$j);
	# AA1: denote that AA contains only one connected component
	# AA2: denote that AA contains two connected components (each one connects to s and t,respectively; s and t are disconnected in the induced subgraph of DS)
	# PE:  denote that G contains only s, t vertices and parallel edges between them; thus, the DS of G-{s,t} is an empty set
	for ($k=0 ; $k < @OP; $k++){
		if ($OP[$k] eq 'l'){ # leaf node (single edge)
			$AA1[$k]=1; $AA2[$k]=0;
			$BB[$k]=0;
			$AB[$k]=$BA[$k]=1;
			$AC[$k]=$CA[$k]=0;
			$BC[$k]=$CB[$k]=0;
			$CC[$k]=1; 
			$PE[$k]=1;
		}else{
			$i=$L[$k];
			$j=$R[$k];
			if($OP[$k] eq 'p'){ # parallel operation
				$AA1[$k]=$AA1[$i]*$AA1[$j]+$AA1[$i]*$AA2[$j]+$AA2[$i]*$AA1[$j];
				$AA2[$k]=$AA2[$i]*$AA2[$j];				
				$AB[$k]=$AB[$i]*$AB[$j]+$AB[$i]*$AC[$j]+$AC[$i]*$AB[$j];								
				$BA[$k]=$BA[$i]*$BA[$j]+$BA[$i]*$CA[$j]+$CA[$i]*$BA[$j];				
				$BB[$k]=$BB[$i]*$PE[$j]+$PE[$i]*$BB[$j];				
				$AC[$k]=$AC[$i]*$AC[$j];
				$CA[$k]=$CA[$i]*$CA[$j];				
				$BC[$k]=$BC[$i]*$PE[$j]+$PE[$i]*$BC[$j];				
				$CB[$k]=$CB[$i]*$PE[$j]+$PE[$i]*$CB[$j];							
				$CC[$k]=$CC[$i]*$PE[$j]+$PE[$i]*$CC[$j];
				$PE[$k]=$PE[$i]*$PE[$j];				
			}elsif($OP[$k] eq 's'){ # series operation				
				$AA1[$k]=$AA1[$i]*$AA1[$j];
				$AA2[$k]=$AA1[$i]*$AA2[$j]+$AA2[$i]*$AA1[$j]+$AC[$i]*$BA[$j]+$AB[$i]*$CA[$j]+$AB[$i]*$BA[$j];				
				$AB[$k]=$AA1[$i]*$AB[$j];
				$BA[$k]=$BA[$i]*$AA1[$j];
				$BB[$k]=$BA[$i]*$AB[$j];			
				$AC[$k]=$AA1[$i]*$AC[$j]+$AB[$i]*$PE[$j];
				$CA[$k]=$CA[$i]*$AA1[$j]+$PE[$i]*$BA[$j];;
				$BC[$k]=$BA[$i]*$AC[$j];
				$CB[$k]=$CA[$i]*$AB[$j];
				$CC[$k]=$CA[$i]*$AC[$j];
				$PE[$k]=0;
			}else{ # dangling operation
				$AA1[$k]=$AA1[$i]*$AA1[$j]+$AA1[$i]*$AB[$j];
				$AA2[$k]=$AA2[$i]*$AA1[$j]+$AA2[$i]*$AB[$j];				
				$BA[$k]=0;
				$AB[$k]=$AB[$i]*$AA1[$j]+$AB[$i]*$AB[$j];;
				$BB[$k]=0;				
				$CA[$k]=0;
				$AC[$k]=$AC[$i]*$AA1[$j]+$AC[$i]*$AB[$j];;				
				$BC[$k]=0;				
				$CB[$k]=0;							
				$CC[$k]=0;
				$PE[$k]=0;
			}
		}	
	} # for
	return($AA1[$k-1]+$AB[$k-1]+$BA[$k-1]+$BB[$k-1]);
} # end of CDS


sub random_select_2 {
	local(*tree_node)=@_;
	my($s,$i,$i1,$i2,$n1,$n2);
			
	$s=$tree_node->size;
	$i1=$i2=int(rand($s));#range [0..s-1]
	while ($i2 == $i1){
		$i2=int(rand($s));#range [0..s-1]
	}
	
	$i=0;
	for $e ($tree_node->elements) {
		$n1=$e if ($i==$i1);
		$n2=$e if ($i==$i2);
		$i++;
	}
	return($n1, $n2);
}

sub new_g{
	my($i,$u,$v,$tree_node,$n1,$n2,$e);
	my(@s,@t,@g);
	
	return(0) if ($m < 2);
	
	@OP=@L=@R=();  # reset	
	$tree_node = Set::Scalar->new;
	for($i=0,$v=0 ; $i < $m ; $i++, $v+=2){
		$g[$i] = Graph::Undirected->new(multiedged => 1);
		$g[$i]->add_edges($v,$v+1);
		$s[$i]=$v;
		$t[$i]=$v+1;
		$OP[$i]='l';  # leaf node
		$L[$i]=$R[$i]='';
		$tree_node->insert($i);
	} 
	
	while ($tree_node->size >= 2){
		$g[$i] = Graph::Undirected->new(multiedged => 1);
		($n1, $n2)=random_select_2(\$tree_node);
		$L[$i]=$n1;
		$R[$i]=$n2;	
	# working for a simple graph	
	#	if ( $g[$n1]->has_edge($s[$n1],$t[$n1]) && $g[$n2]->has_edge($s[$n2],$t[$n2])){		
	#		$OP[$i]='s';	
	#	}elsif (rand(1) < 0.5){
	
	# working for a multi-graph
		$r=rand(1);		
		if ($r < 1/3){ 
			$OP[$i]='s'; # series composition
		}elsif($r>=1/3 and $r<2/3){
			$OP[$i]='p'; # parallel composition
		}else{
			$OP[$i]='d';  #dangling composition
		}
	
		if ($OP[$i] eq 's' || $OP[$i] eq 'd'){  # series or dangling composition
			$s[$i]=$s[$n1];
			if ($OP[$i] eq 's'){
			  $t[$i]=$t[$n2];
			}else{ # op='d'
				$t[$i]=$t[$n1];
			}
			$g[$i]=$g[$n1]; # first, copy the graph of the left child;		
			foreach $e ($g[$n2]->edges){ #second, append the graph of the right child 
				$u=$$e[0]; $v=$$e[1];
				if ($u==$s[$n2]){ 
				  if ($OP[$i] eq 's'){
					  $g[$i]->add_edge($t[$n1],$v);# change the index of s node of g[n2] to the index of t of g[n1]
					}else{ # op='d'
					  $g[$i]->add_edge($s[$n1],$v);# change the index of s node of g[n2] to the index of s of g[n1]					
					}					
				}elsif($v==$s[$n2]){
				  if ($OP[$i] eq 's'){				
				 	  $g[$i]->add_edge($t[$n1],$u);# change the index of s node of g[n2] to the index of t of g[n1]
					}else{ # op='d'
					  $g[$i]->add_edge($s[$n1],$u);# change the index of s node of g[n2] to the index of s of g[n1]										
					}
				}else{
					$g[$i]->add_edge($u,$v);  # no change
				}			
			}
		}else{ # parallel composition
			$s[$i]=$s[$n1];
			$t[$i]=$t[$n1];
		
			$g[$i]=$g[$n1]; # first, copy the graph of the left child;		
			foreach $e ($g[$n2]->edges){ #second, append the graph of the right child 
				$u=$$e[0]; $v=$$e[1];
				if ($u==$s[$n2]){
					$u=$s[$n1];
				}elsif($u==$t[$n2]){
					$u=$t[$n1];
				}
				if ($v==$s[$n2]){
					$v=$s[$n1];
				}elsif($v==$t[$n2]){
					$v=$t[$n1];
				}		
				$g[$i]->add_edge($u,$v); 
			} # foreach e	
		}

		$tree_node->insert($i);	
		$tree_node->delete($n1,$n2);
		$i++;
	} # while		
	
	$j=1;
	foreach $u ($g[$i-1]->vertices){ #relabeled vertices in the sequence of 1, 2, 3...
	  $label[$u]=$j++;		
	}	
	$g = Graph::Undirected->new(multiedged => 1);
	foreach $e ($g[$i-1]->edges){ #construct the graph g with the new labels
		$u=$$e[0]; $v=$$e[1];
		$g->add_edge($label[$u],$label[$v]);
	}
	$n=$g->vertices;  
	return(1);
}


sub brute_force { # working for a multi-graph

	$max=2**$g->vertices-1;
	@is_set=();
	@is_set = map { Set::Scalar->new() } 0..$max;

	#for checking independent perfect dominating sets
	my $all_v= Set::Scalar->new(1..$n); # all vertices
	my $mis;  # maximal independent sets
	my $ipds_flag;
	my $nipds=0;
	$nds=0; # for counting dominating sets
	$ncds=0;# for counting connected dominating sets
	$ntds=0;# for counting total dominating sets
	$nis=0; # for counting independent sets
	@max_is_tag=();
	%hsize=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		
		$dominating_vertices= Set::Scalar->new;  # for counting dominating sets
		$total_dominating_vertices= Set::Scalar->new;  # for counting total dominating sets		
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];		
					$dominating_vertices->insert($$a[0],$$a[1]);# for counting dominating sets
					
					if ($$a[0] == $vs ){
						$total_dominating_vertices->insert($$a[1]);# for counting total dominating sets
					}else{
						$total_dominating_vertices->insert($$a[0]);# for counting total dominating sets
					}					
				}  
				$is_set[$num]->insert($vs);
			}
		}
		if ($dominating_vertices->size == scalar($g->vertices)){ # for counting dominating sets
		  $nds++; 
			
			#check if it is a connected dominating set			
			@dv = $is_set[$num]->elements;		#for counting connected dominating sets
			my $induced_subgraph = $g->subgraph(\@dv);      #for counting connected dominating sets
			if ($induced_subgraph->is_connected){           #for counting connected dominating sets
			  $ncds++;                               #for counting connected dominating sets
			}                                       #for counting connected dominating sets			
			
			#check if it is a total dominating set			
			if ($total_dominating_vertices->size == scalar($g->vertices)){ # for counting total dominating sets
				$ntds++;
			}
		}
		# check if it is an independent set		
		$is=$is_set[$num];
		$independent_flag=1;
		foreach $v ($is->elements){
			foreach $u ($is->elements){
			 next if ($u == $v);
			 $independent_flag=0 if ( $g->has_edge($u,$v));
			}
		}
		
		if ( $independent_flag == 1){ # $is_set[$num] is an independent set
			$nis++;       
			$flag=1;
			foreach $i (0..$num-1){
				if ($max_is_tag[$i]==1){
					$mvi=$is_set[$i];
					if ( $is->is_proper_superset($mvi) ){
						$max_is_tag[$i]=0;
						$flag=1;
					}elsif ( $is->is_proper_subset($mvi) ){
						$flag=0;
						break;
					}
				}
			}
			if ($flag==1){
				$max_is_tag[$num]=1;				
				#check independent perfect dominating sets
				$vc=$all_v-$is; # set difference
				$ipds_flag=1;
				for my $u ($vc->elements) { # u is not in mis
					$dominated=0;
					for my $i ($is->elements) { # i is in mis
						if ($g->has_edge($i, $u)){ # u and i are adjacent
							$dominated++; # i dominates u
						}
					}
					if ($dominated != 1){# u is dominated by more than one vertex
						$ipds_flag=0;
						break;
					}
				}
				if ($ipds_flag == 1){  # $mis is a independent perfect dominating sets
					$nipds++;
				}        
			}
		}
	}
	$nmis=0;
	for ($i=0; $i <= $max ; $i++){
		if ($max_is_tag[$i]==1){
			$nmis++;
		}	
	}	
	return($nis,$nmis,$nipds,$nds,$ncds,$ntds); 
}
