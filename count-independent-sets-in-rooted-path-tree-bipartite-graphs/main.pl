#!/usr/bin/perl
#
# Count independent sets and maximal independent sets in a rooted path-tree bipartite graph
#
#
# by Min-Sheng Lin
#
use strict;
use Set::Scalar;
use Tree::Simple;
use Graph;

# tree structure
our $max_node_size=4;
our $max_children=4;
our $max_depth=4;
our $max_extra=2;
our $max_from_parent=2;

our $null=Set::Scalar->new();
our $ny;  # the number of y vertices
our $nx;  # the number of x vertices
our (@y_start, @y_end, @post_order, @beta, @adj);
our ($xr, $x0); # xr: root node of the tree; x0: dummy root node 
my $test=0;
while ( $test++ < 20 ){ # test 20 random instances	
	print "\n== test #$test: rooted path-tree bipartite graph ==\n";	
	# create a random rooted path-tree bipartite graph
	$xr=&create_tree(); # the rooted directed tree of a bipartite rooted directed path graph  
	next if ($nx+$ny > 14)  ;	
	&print_tree($xr);		
	
	# count ISs and MISs by using brute-force approach
	my ($ISx,$MISx)=&brute_force();
		
	# count ISs and MISs by our approach
	#   add the dummy root node
	$x0 = Tree::Simple->new($null); # empty set 
	$x0->setUID($nx+1);
	$x0->addChild($xr);
  
	#   compute the postorder traversal
	@post_order=();
	&post_order_travesal($x0); # setup @post_order
	
	#   compute beta
	@y_start=@y_end=();
	&dfs_for_y_boundary($x0);
	&count_beta($x0);
	
	#  count IS and MIS
	my ($IS1)=&count_IS();  
	my ($MIS1)=&count_MIS();  
	
	print "the brute-force algorithm: #IS=$ISx #MIS=$MISx\n";
	print "   our proposed algorithm: #IS=$IS1 #MIS=$MIS1\n";
	
	if ($ISx != $IS1 || $MISx != $MIS1){
		print "An error occured. Stop!\n";
		exit;
	}
	$xr->DESTROY();
	print "\n";
} # while test
print "\n Tests completed successfully.\n";


#---------------------------------------------------------------------
# count independent sets (ISs) in a rooted path-tree bipartite graph
# time complexity: O(|nx|^2*|ny|)
#---------------------------------------------------------------------
sub count_IS { 			
	my @is;
	for my $i (0 .. $#post_order-1){  # skip the dummy root node
		my $xi=$post_order[$i];		
		my $A=1; #bounday condition if xi is a leaf		 
		foreach my $c ($xi->getAllChildren()){
			$A *= $is[$c->getUID][$xi->getUID];
		} # foreach child	
	
		my $xk=$xi;
		do {    	
			$xk=$xk->getParent;	   
			my $B=2**$beta[$xi->getUID][$xk->getUID];#bounday condition if xi is a leaf		 
			foreach my $c ($xi->getAllChildren()){
				$B *= $is[$c->getUID][$xk->getUID];
			} # foreach child       
			$is[$xi->getUID][$xk->getUID]=$A+$B;	   
		} until ($xk->isRoot); # do xk
	} # for i	
    
	return($is[$xr->getUID][$x0->getUID]);	
}

#-----------------------------------------------------------------------------
# count maximal independent sets (MISs) in a rooted path-tree bipartite graph
# time complexity: O(max{|nx|^2*|ny|,|nx|^3})
#-----------------------------------------------------------------------------
sub count_MIS { 	
	my (@mis,@misx);	
	for my $i (0 .. $#post_order-1){  # skip the dummy root node
		my $xi=$post_order[$i];
		# compute A for both  mis and misx
		my $A=1;  #bounday condition if xi is a leaf		 
		foreach my $c ($xi->getAllChildren()){
			$A *= $mis[$c->getUID][$xi->getUID];		   
		}

		my $xk=$xi;
		do {    
			$xk=$xk->getParent;			
			# compute mis by Lemma 2
			#   compute B1 for mis
			my $B1=1;	#bounday condition if xi is a leaf		 	 
			foreach my $c ($xi->getAllChildren()){
				$B1 *= $mis[$c->getUID][$xk->getUID];		   
			} 
			#   compute B2 for both mis and misx
			my $B2=1;  #bounday condition if xi is a leaf		 
			foreach my $c ($xi->getAllChildren()){
				$B2 *= $misx[$c->getUID][$xi->getUID][$xk->getUID];
			}

			if ($beta[$xi->getUID][$xk->getUID] != 0){
				$mis[$xi->getUID][$xk->getUID]=$A+$B1; # Eq. (1)
			}else{		   
				$mis[$xi->getUID][$xk->getUID]=$A+$B1-$B2; # Eq. (2)
			}		 

			# compute misx by Lemma 3
			for (my $xj=$xi->getParent; $xj->getUID != $xk->getUID ; $xj=$xj->getParent){	# note: xi < xj < xk 
				if ( $beta[$xi->getUID][$xj->getUID] != $beta[$xi->getUID][$xk->getUID]   ){
					$misx[$xi->getUID][$xj->getUID][$xk->getUID]=$A;  # Eq. (3)
				}else{  
					# compute B1 for misx
					$B1=1;	#bounday condition if xi is a leaf		 	 
					foreach my $c ($xi->getAllChildren()){
						$B1 *= $misx[$c->getUID][$xj->getUID][$xk->getUID];		   
					}			 
					if ($beta[$xi->getUID][$xk->getUID] != 0){# or $beta[$xi->getUID][$xj->getUID] != 0)
						$misx[$xi->getUID][$xj->getUID][$xk->getUID]=$A+$B1; # Eq. (4)
					}else{
						$misx[$xi->getUID][$xj->getUID][$xk->getUID]=$A+$B1-$B2; # Eq. (5)
					}			 
				}# else 
			} #for xj			
		} until ($xk->isRoot); # do xk
	} # for i	
  
	return($mis[$xr->getUID][$x0->getUID]);
}

#------------------------------------------------------------------------------
# create the rooted directed tree of a random rooted path-tree bipartite graph
#------------------------------------------------------------------------------
sub create_tree {
	my $x=0; # reset the tree node id;
	$ny=$nx=0;  # reset;
	@adj=(); # reset;
	#my($n,$s,$child,$fp,$fps,$ki,$ksize,@queue,@knode_member, @kinode_member);
	my $y=int(rand($max_node_size))+1; # 1 ~ $max_node_size 
	$xr = Tree::Simple->new(Set::Scalar->new(1..$y));
	$xr->setUID(++$x);
	for (my $j=1; $j<=$y; $j++){
		$adj[$x][$j]=1;
	}	
	push(my @queue,$xr);
	while (my $k=shift(@queue)){
		next if ( $k->getDepth() == $max_depth );
		my $child=int(rand($max_children+1)); # 0~ $max_children	
		my @knode_member=$k->getNodeValue()->elements();
		my $ksize=$k->getNodeValue()->size();	
		my $endflag=0; 
		my $i=0;    
		my $fps=0;
		while ($i < $child && !$endflag){
			my $fp=int(rand($max_from_parent))+1;	  
			$fps += $fp;
			if ($fps > $ksize){
				$endflag=1;
			}else{
				my @kinode_member=();		
				for (my $j=0,my $s=0; $s < $fp; $j=($j+1)%$ksize){     
					next if (!$knode_member[$j]);         
					push(@kinode_member,$knode_member[$j]);		  
					$knode_member[$j]=0;		  
					$s++;		  
				}#for		
				my $extra=int(rand($max_extra));	  		
				for (my $j=0; $j < $extra ; $j++){
					push(@kinode_member,++$y);
				}  

				my $ki=Tree::Simple->new(Set::Scalar->new(@kinode_member),$k);
				$ki->setUID(++$x);
		
				foreach my $j (@kinode_member){
					$adj[$x][$j]=1;
				}		
				push(@queue,$ki);
			}#else
			$i++; # next child
		}#while $i < $child
	} # while shift queue 
	$ny=$y;      # the number of y vertices  
	$nx=$x;      # he number of x vertices 
	return($xr);
} # create tree

sub dfs_for_y_boundary{
	my ($t)=@_;  
	return if (!$t);
	foreach my $c ($t->getAllChildren()){
		&dfs_for_y_boundary($c); 
	} 
	#print $t->getNodeValue();
	my $s=$t->getNodeValue();
	my $x=$t->getUID;
	foreach my $y ($s->elements){   
		if ($y_start[$y] && $y_end[$y]){
			$y_start[$y]=$x;
		}else{
			$y_start[$y]=$y_end[$y]=$x;
		}	
	}	
} #dfs_for_y_boundary

sub count_beta {
	my($xroot)=@_;	
	@beta=();  # reset	
	$xroot->traverse(sub {
		my ($xi) = @_;
		my ($x,$y,$xj,$count);
	  	  
		my $ends = Set::Scalar->new;
		foreach $y ($xi->getNodeValue->elements){
			if ($y_end[$y]==$xi->getUID){
				$ends->insert($y);
			}
		}	   
		$count=0;	   
		for($xj=$xi; !$xj->isRoot ; $xj=$xj->getParent  ){		    
			$beta[$xi->getUID][$xj->getUID]=$count;
			foreach $y ($xj->getNodeValue->elements){
				if ($y_start[$y]==$xj->getUID && $ends->has($y)){
					$count++;
				}
			}# for each y
		}
		$beta[$xi->getUID][$xj->getUID]=$count; # xj is the dummy root node
	}); # end of traverse
	print "\n";	 
}

sub brute_force{  
	my $g = Graph::Undirected->new();
	for (my $a=1; $a<=$nx; $a++){ 
		for (my $b=1; $b<=$ny; $b++){      
			if ($adj[$a][$b]){
				$g->add_edges([$ny+$a,$b]);  #a is shifted ny positions
			}#if
		}# for u
	}#for v
	my %edge=();  
	print "nx=$nx ny=$ny | graph g= $g\n";
  
	return if ($nx+$ny > 14);
  
	my $max=2**$g->vertices-1;	
	my @vc_set = map { Set::Scalar->new() } 0..$max;
	
	my $mis;  # maximal independet sets

	my $number_vc=0;
	my @min_vc_tag=();

	foreach my $num (0..$max){
		my $bits = unpack ( "B*", pack("N",$num) );		
		my @bit =split(//,$bits);
		@bit = reverse(@bit);
		my %cover=();
		foreach my $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				my @edges=$g->edges_at($vs);
				foreach my $a (@edges){
					my $edge=$$a[0].'-'.$$a[1];
					$cover{$edge}=1;
				}  
				$vc_set[$num]->insert($vs);
			}
		} #foreach vs
		my @cover_edge=keys %cover;
      
		my $vc=$vc_set[$num];

		if ( scalar(@cover_edge) == scalar($g->edges) ){
			$number_vc++;       
			$min_vc_tag[$num]=1;           			
			foreach my $i (0..$num-1){
				if ($min_vc_tag[$i]==1){
					my $mvi=$vc_set[$i];
					if ( $vc->is_proper_subset($mvi) ){
						$min_vc_tag[$i]=0;
					} elsif ( $vc->is_proper_superset($mvi) ){
						$min_vc_tag[$num]=0;	
						last;
					}
				}
			} #foreach    
		} #if scalar
	}#foreach $num

	my $number_min_vc=0;
	for (my $i=0; $i <= $max ; $i++){
		if ($min_vc_tag[$i]==1){
			$number_min_vc++;
		}
	}
	return($number_vc,$number_min_vc);
}# end sub search_all


sub sortbysizekey{
	return $a<=>$b;
}

sub print_tree{
	my($tree)=@_;
	print "kr=\n",$tree->getUID,$tree->getNodeValue(),"\n";
	$tree->traverse(sub {
		my ($_tree) = @_;
		print "\t";
		print (("\t" x $_tree->getDepth()),$_tree->getUID, $_tree->getNodeValue(), "\n");
	});
}

sub post_order_travesal{
	my ($t)=@_;   
	my ($c);   
	return if (!$t); # null node
	foreach $c ($t->getAllChildren()){
		&post_order_travesal($c); 
	}
	push(@post_order,$t); 
}# end of post_order_travesal
