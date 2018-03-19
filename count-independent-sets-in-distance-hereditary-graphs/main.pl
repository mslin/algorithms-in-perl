#!/usr/bin/perl
#
# Count independent sets, independent dominating sets (maximal independent sets),
# and independent perfect dominating sets in a distance-hereditary graph
#
# Time complexity: O(n)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=8; 	# problem size
$p1=1; $p2=1; $p3=1;  # the ratio of "pendant : false twins : true twins"
@op=();
@twin=();
$g=();
 
while ( $test++ < 20 ){ # test 20 random instances	
	&new_g(); # create a random distance hereditary graph
		
	print "\n== test$test: distance hereditary: ==\n";	
	print "g : $g\n";
	print "op: ";
	foreach $v (2..$n){
		print "$v$op[$v]$twin[$v]  ";
	}
	print "\n";
	
	print "our proposed algorithm	 : ";		
	$IS1=&IS();	
	$IDS1=&IDS();
	$IPDS1=&IPDS(); 
	print "IS=$IS1, IDS=$IDS1, IPDS=$IPDS1\n";
	
	print "the brute-force algorithm: ";
	($IS2,$IDS2,$IPDS2)=&brute_force();
	print "IS=$IS2, IDS=$IDS2, IPDS=$IPDS2\n";

	if( $IS1!=$IS2 || $IDS1 != $IDS2 || $IPDS1 != $IPDS2){
		print "An error occured. Stop!\n";
		exit;
	}
}										 
print "\n Tests completed successfully.\n";

# count independent sets (ISs) in a distance-hereditary graph
sub IS {
	my (@ISa, @ISb, $ISa, $ISb, $i, $j);
	for ($i=1; $i<=$n ; $i++){
		$ISa[$i]=1;
		$ISb[$i]=1;
	}
	for ($j=$n ; $j>=2 ;$j--){
		$i=$twin[$j];
		if($op[$j] eq 'T'){# op = truth twin
			$ISa=$ISa[$i]*$ISb[$j]+$ISb[$i]*$ISa[$j]; 
			$ISb=$ISb[$i]*$ISb[$j];		
		}elsif($op[$j] eq 'F'){# op = false twin
			$ISa=$ISa[$i]*$ISb[$j]+$ISb[$i]*$ISa[$j]+$ISa[$i]*$ISa[$j]; 						
			$ISb=$ISb[$i]*$ISb[$j];		
		}else{# op = pendant 
			$ISa=$ISa[$i]*$ISb[$j]; 
			$ISb=$ISb[$i]*($ISa[$j]+$ISb[$j]);
		}
		$ISa[$i]=$ISa;
		$ISb[$i]=$ISb;		
	}	
	return($ISa[1]+$ISb[1]);
}

# count independent dominating sets (IDSs) in a distance-hereditary graph
sub IDS {
	my (@IDSa,@IDSb,@IDSc, $IDSa, $IDSb, $IDSc, $i, $j);
	for ($i=1; $i<=$n ; $i++){
		$IDSa[$i]=1;
		$IDSb[$i]=0;
		$IDSc[$i]=1;		
	}
	for ($j=$n ; $j>=2 ;$j--){
		$i=$twin[$j];
		
		if($op[$j] eq 'T'){# op = truth twin
			$IDSa=$IDSa[$i]*($IDSb[$j]+$IDSc[$j])+($IDSb[$i]+$IDSc[$i])*$IDSa[$j]; 
			$IDSb=$IDSb[$i]*$IDSb[$j];		
			$IDSc=$IDSb[$i]*$IDSc[$j]+$IDSc[$i]*$IDSb[$j]+$IDSc[$i]*$IDSc[$j];			
		}elsif($op[$j] eq 'F'){# op = false twin
			$IDSa=$IDSa[$i]*$IDSb[$j]+$IDSb[$i]*$IDSa[$j]+$IDSa[$i]*$IDSa[$j]; 
			$IDSb=$IDSb[$i]*$IDSb[$j];		
			$IDSc=$IDSb[$i]*$IDSc[$j]+$IDSc[$i]*$IDSb[$j]+$IDSc[$i]*$IDSc[$j];			
		}else{# op = pendant 
			$IDSa=$IDSa[$i]*($IDSb[$j]+$IDSc[$j]); 						
			$IDSb=$IDSb[$i]*$IDSb[$j]+($IDSb[$i]+$IDSc[$i])*$IDSa[$j];		
			$IDSc=$IDSc[$i]*$IDSb[$j];
		}	
		$IDSa[$i]=$IDSa;
		$IDSb[$i]=$IDSb;
		$IDSc[$i]=$IDSc;
	}		
	return($IDSa[1]+$IDSb[1]);
}

# count independent perfect dominating sets (IPDSs) in a distance-hereditary graph
sub IPDS {
	my (@IPDS,@IPDSb,@IPDSc, $IPDS, $IPDSb, $IPDSc);
	for ($i=1; $i<=$n ; $i++){
		$IPDSa[$i]=1;
		$IPDSb[$i]=0;
		$IPDSc[$i]=1;		
	}
	for ($j=$n ; $j>=2 ;$j--){
		$i=$twin[$j];	
		if($op[$j] eq 'T'){# op = truth twin
			$IPDSa=$IPDSa[$i]*$IPDSc[$j]+$IPDSc[$i]*$IPDSa[$j]; 
			$IPDSb=$IPDSb[$i]*$IPDSb[$j];		
			$IPDSc=$IPDSc[$i]*$IPDSc[$j];
		}elsif($op[$j] eq 'F'){# op = false twin
			$IPDSa=$IPDSa[$i]*$IPDSb[$j]+$IPDSb[$i]*$IPDSa[$j]; 
			$IPDSb=$IPDSb[$i]*$IPDSb[$j];		
			$IPDSc=$IPDSc[$i]*$IPDSc[$j];
		}else{# op = pendant 
			$IPDSa=$IPDSa[$i]*$IPDSc[$j]; 						
			$IPDSb=$IPDSb[$i]*$IPDSb[$j]+$IPDSc[$i]*$IPDSa[$j];		
			$IPDSc=$IPDSc[$i]*$IPDSb[$j];		
		}	
		$IPDSa[$i]=$IPDSa;
		$IPDSb[$i]=$IPDSb;
		$IPDSc[$i]=$IPDSc;
	}		
	return($IPDSa[1]+$IPDSb[1]);
}

#create a random distance-hereditary graph
sub new_g{
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);

	@op=();
	@twin=();
	
	$op[2]='P'; # default: add a new pendant vertex 2 to vertex 1 (or T truth twins op)
	$twin[2]=1;
	$g->add_edges([1,2]);
	
	for ($v=3; $v <=$n ; $v++){
		$u=int(rand($v-1))+1;#range [1..v-1]
		$twin[$v]=$u;
		
		$r=rand(1);
		if ($r < $p1/($p1+$p2+$p3)){ # pendant op
			$op[$v]='P';			
			$g->add_edges([$v,$u]);
		}elsif ( $r < ($p1+$p2)/($p1+$p2+$p3)){ # false twins op
			$op[$v]='F';			
			foreach $w ( $g->neighbours($u)){
				$g->add_edges([$v,$w]);	
			}			
		}else{# true twins op
			$op[$v]='T';
			foreach $w ( $g->neighbours($u)){
				$g->add_edges([$v,$w]);	
			}			
			$g->add_edges([$v,$u]);
		}
	}# for v
}


sub brute_force{
	$max=2**$g->vertices-1;
	@vc_set=();
	@vc_set = map { Set::Scalar->new() } 0..$max;

	#for checking independent perfect dominating sets
	my $all_v= Set::Scalar->new(1..$n); # all vertices
	my $mis;  # maximal independet sets
	my $ipds_flag;
	my $nipds=0;

	$nvc=0;
	@min_vc_tag=();
	%hsize=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		%cover=();
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];
					$cover{$edge}=1;
				}  
				$vc_set[$num]->insert($vs);
			}
		}
		@cover_edge=keys %cover;      
		$vc=$vc_set[$num];
		if ( scalar(@cover_edge) == scalar($g->edges) ){
			$nvc++;       
			$flag=1;
			foreach $i (0..$num-1){
				if ($min_vc_tag[$i]==1){
					$mvi=$vc_set[$i];
					if ( $vc->is_proper_subset($mvi) ){
						$min_vc_tag[$i]=0;
						$flag=1;
					}elsif ( $vc->is_proper_superset($mvi) ){
						$flag=0;
						break;
					}
				}
			}
			if ($flag==1){
				$min_vc_tag[$num]=1;				
				#check independent perfect dominating sets
				$mis=$all_v-$vc; # set difference
				$ipds_flag=1;
				for my $u ($vc->elements) { # u is not in mis
					$dominated=0;
					for my $i ($mis->elements) { # i is in mis
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
	$nmvc=0;
	for ($i=0; $i <= $max ; $i++){
		if ($min_vc_tag[$i]==1){
			$nmvc++;
		}	
	}	
	return($nvc,$nmvc,$nipds); # note: |VC|=|IS| and |MVC|=|IDS|
}
