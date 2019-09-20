

import java.io.Serializable;

public class EvidenceInfo implements Serializable {
	
	private String residentNode;
	private ArgumentInfo[] arguments;
	private String state;
	
	public String getResidentNode() {
		return residentNode;
	}

	public void setResidentNode(String residentNode) {
		this.residentNode = residentNode;
	}

	public ArgumentInfo[] getArguments() {
		return arguments;
	}
	
	public void setArguments(ArgumentInfo[] arguments) {
		this.arguments = arguments;
	}

	public String getState() {
		return state;
	}

	public void setState(String state) {
		this.state = state;
	}

}